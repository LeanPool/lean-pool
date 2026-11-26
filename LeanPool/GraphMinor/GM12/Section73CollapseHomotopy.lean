/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73DiscSupportedHomotopy
import LeanPool.GraphMinor.GM12.Section73CollapseComposition
import LeanPool.GraphMinor.GM11.Section6
public import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# A disc-supported collapse preserves the homotopy class of a curve

For the selected-inside comparison in XII (7.3), Claim (1),
page 262, the star lies in the interior of its supporting disc.
The exact fibre condition and the fixed outside imply that the
collapse preserves this interior. Interpolate in the supporting
disc and extend by the identity. Any curve and its collapsed
image are then homotopic while avoiding all points outside the
curve and the supporting disc.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- A collapse whose fibres lie in a supporting disc preserves
the homotopy class of a closed curve, with the homotopy contained
in the curve together with that disc. This is the controlled
deformation used for XII (7.3), Claim (1), page 262. -/
theorem closedCurve_homotopic_under_disc_collapse
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {D A Z : Set S} (hD : IsClosedDisc D)
    (hAD : A ⊆ discInt D) (f : C(S, S))
    (hfix : ∀ x ∉ discInt D, f x = x)
    (hfibre : ∀ x y, f x = f y ↔ x = y ∨ (x ∈ A ∧ y ∈ A))
    (φ : C(Circle, S)) (hφZ : range φ ⊆ Z) (hDZ : D ⊆ Z) :
    ClosedCurvesHomotopicIn Z φ (f.comp φ) := by
  have hint : discInt D = interior D := by
    rw [discInt, ← IsClosedDisc.frontier_eq_discBd hS hD, frontier, hD.isClosed.closure_eq]
    ext x
    constructor
    · rintro ⟨hxD, hx⟩
      by_contra hxI
      exact hx ⟨hxD, hxI⟩
    · intro hxI
      exact ⟨interior_subset hxI, fun hx => hx.2 hxI⟩
  have hpres := (collapse_image_diff_eq hfibre hfix hAD).1
  have hmap : ∀ x ∈ D, f x ∈ D := by
    intro x hxD
    by_cases hxI : x ∈ discInt D
    · exact Surface.discInt_subset D ((hpres x).mpr hxI)
    · exact (hfix x hxI).symm ▸ hxD
  have hfix' : ∀ x ∉ interior D, f x = x := by
    rw [← hint]
    exact hfix
  exact closedCurve_homotopic_of_disc_supported_map hD f hmap hfix' φ hφZ hDZ

end GraphMinor.GM12
