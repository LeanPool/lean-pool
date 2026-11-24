/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.Surface.Jordan
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-!
# Putting the planar source configuration in a surface chart

The proof of XII (4.5), page 252, first constructs its crossing
drawing in the plane and then in the surface. The plane is
homeomorphic to an open unit disc. Compose this homeomorphism
with the inverse of a chart at any point of the closed surface.
The result is an open embedding, so all arc, disc, intersection,
and local crossing data can be carried into the surface.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Every nonempty closed surface contains an openly embedded
copy of the plane. This carries the source configuration of
XII (4.5), page 252, into the surface before star thickening. -/
theorem exists_plane_openEmbedding {S : Type*} [TopologicalSpace S] [Nonempty S]
    (hS : IsClosedSurface S) : ∃ f : ℂ → S, Topology.IsOpenEmbedding f := by
  classical
  let y : S := Classical.choice inferInstance
  obtain ⟨U, hU, -, ⟨h⟩⟩ := hS.2.2 y
  let e : ℂ ≃ₜ U := complexPlane.toHomeomorph.trans (Homeomorph.unitBall.trans h.symm)
  exact ⟨(fun z => (e z).val), hU.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding⟩

end GraphMinor.GM12
