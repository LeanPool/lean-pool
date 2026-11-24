/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.Surface.ArcTools

/-!
# Lines under embeddings between different spaces

Parametrise a line by a closed interval and compose its parametrisation
with the embedding. The resulting arc has the image line as its range
and the images of the original ends as its ends. This is used to move
the wall's coordinate lines into a sphere in XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Topology GraphMinor.Surface
universe u v

/-- An embedding carries a line to a line with the corresponding ends.
The two spaces may belong to different universes. -/
theorem isLineWithEnds_image_embedding
    {S : Type u} {T : Type v} [TopologicalSpace S] [TopologicalSpace T]
    [T2Space T] {j : S → T} (hj : IsEmbedding j)
    {L : Set S} {a b : S} (hL : IsLineWithEnds L a b) :
    IsLineWithEnds (j '' L) (j a) (j b) := by
  obtain ⟨p,hp,rfl,rfl,rfl⟩ := hL.exists_arc
  have hArc : IsArcMap (j ∘ p) := ⟨hj.continuous.comp hp.1,hj.injective.comp hp.2⟩
  have h := hArc.isLineWithEnds
  rwa [range_comp] at h

end GraphMinor.GM16
