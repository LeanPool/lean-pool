/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Compactness.Compact

/-!
# The complement of a contracted drawing

For the radial-star contraction in XII (7.3), page 261, the collapsed
set lies inside the drawing. The collapse therefore identifies no
points of its complement. Since a continuous map from a compact
space to a Hausdorff space is closed, the induced bijection of
complements is a homeomorphism. This lets regions pass through the
contraction without changing their topology.
-/

public section

namespace GraphMinor.GM12

open Set Topology

/-- A continuous surjective collapse supported inside a set gives
a homeomorphism of its complement to the complement of its image.
This transfers radial regions through the contraction in XII (7.3). -/
theorem exists_homeomorph_collapse_complement
    {S : Type*} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    {A B : Set S} (hAB : A ⊆ B) (f : C(S, S)) (hsurj : Function.Surjective f)
    (hfibre : ∀ x y, f x = f y ↔ x = y ∨ (x ∈ A ∧ y ∈ A)) :
    ∃ e : ↥(Bᶜ) ≃ₜ ↥((f '' B)ᶜ), ∀ x : ↥(Bᶜ), (e x).val = f x := by
  have hpre : f ⁻¹' (f '' B)ᶜ = Bᶜ := by
    ext x
    constructor
    · intro hx hxB
      exact hx (mem_image_of_mem f hxB)
    · rintro hx ⟨y, hyB, hyx⟩
      rcases (hfibre x y).mp hyx.symm with hxy | hAxy
      · exact hx (hxy ▸ hyB)
      · exact hx (hAB hAxy.1)
  let p := ((f '' B)ᶜ).restrictPreimage f
  have hinj : Function.Injective p := by
    intro x y hxy
    apply Subtype.ext
    have hxy' : f x = f y := congrArg Subtype.val hxy
    rcases (hfibre x y).mp hxy' with hxy' | hAxy
    · exact hxy'
    · exact False.elim (x.property (mem_image_of_mem f (hAB hAxy.1)))
  let e := (Equiv.ofBijective p ⟨hinj, hsurj.restrictPreimage _⟩).toHomeomorphOfContinuousClosed
    f.continuous.restrictPreimage (f.continuous.isClosedMap.restrictPreimage _)
  refine ⟨(Homeomorph.setCongr hpre).symm.trans e, ?_⟩
  intro x
  rfl

end GraphMinor.GM12
