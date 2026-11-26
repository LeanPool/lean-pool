/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4SmallSurface
import LeanPool.GraphMinor.Surface.InvarianceOfDomain
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# A homeomorphic small copy of the surface

The geometric construction of XII (4.5) can be performed on
a small copy of the surface and carried back by a homeomorphism.
The finite chart cover proves that the surface is small. Put
the induced topology on its small model and transfer compactness,
Hausdorffness, and the interior charts through the equivalence.
This preserves the surface hypotheses without a universe bound
in the final result.
-/

public section

namespace GraphMinor.GM12

open Surface

/-- Every closed surface has a homeomorphic closed-surface
copy in the lowest type universe. This permits the geometric
construction of XII (4.5) to be transported to arbitrary
surface universes. -/
theorem exists_small_closed_surface_copy {S : Type*} [TopologicalSpace S]
    (hS : IsClosedSurface S) :
    ∃ (T : Type) (t : TopologicalSpace T),
      Nonempty (@Homeomorph S T inferInstance t) ∧ @IsClosedSurface T t := by
  classical
  let : Small.{0} S := small_of_isClosedSurface hS
  let T : Type := Shrink S
  let : TopologicalSpace T := TopologicalSpace.induced (equivShrink S).symm inferInstance
  let e : T ≃ₜ S := (equivShrink S).symm.toHomeomorphOfIsInducing ⟨rfl⟩
  let : CompactSpace S := hS.1
  let : T2Space S := hS.2.1
  have hc : CompactSpace T := e.symm.compactSpace
  have ht2 : T2Space T := e.isEmbedding.t2Space
  have hi : ∀ x : T, IsInteriorPoint x := fun x =>
    (isInteriorPoint_homeomorph_iff e x).mp (hS.2.2 (e x))
  exact ⟨T, inferInstance, ⟨e.symm⟩, hc, ht2, hi⟩

end GraphMinor.GM12
