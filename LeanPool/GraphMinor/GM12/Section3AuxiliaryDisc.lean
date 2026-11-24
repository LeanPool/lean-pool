/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3DiscRegion
import LeanPool.GraphMinor.GM11.Section4c
import LeanPool.GraphMinor.Surface.DiscMerge
import LeanPool.GraphMinor.Surface.Cap

/-!
# Placing the auxiliary disc away from a forest

For the two-disc case of XII (3.2), page 247, choose an interior
point of the intermediate region outside the feasibility forest.
A drawing contains no open subset of the surface, so such a point
exists. A small coordinate disc stays in that region and misses
the forest. The unique-region lemma makes it disjoint from the
original prescribed discs as well.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 Metric

private theorem exists_closed_disc_subset_open
    {S : Type*} [TopologicalSpace S] (hS : IsClosedSurface S)
    {W : Set S} (hW : IsOpen W) (hne : W.Nonempty) :
    ∃ E : Set S, IsClosedDisc E ∧ E ⊆ W := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨U, h, g, c, hUW, _⟩ := (hS.2.2 x).exists_ballChart hW hx (R := 2) (by norm_num)
  have hsub : closedBall (0 : ℂ) 1 ⊆ ball 0 2 := closedBall_subset_ball (by norm_num)
  have hD : IsClosedDisc (closedBall (0 : ℂ) 1) :=
    (isClosedDisc_of_convex (convex_closedBall 0 1) (by
      rw [interior_closedBall _ one_ne_zero]
      exact ⟨0, by simp⟩) isBounded_closedBall isClosed_closedBall).1
  refine ⟨g '' closedBall 0 1, (c.image_disc hD hsub).1, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  exact hUW (c.gm (hsub hz))

/-- An auxiliary disc inside a third region can be chosen disjoint
from a given drawing, in particular from the feasibility forest.
This is the disc-placement step of XII (3.2), page 247. -/
theorem exists_auxiliary_disc_in_region
    {S ι : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (Γ K : Drawing S) (Δ r : ι → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i))
    (havoid : ∀ i, Γ.U ∩ Δ i = Γ.V ∩ discBd (Δ i))
    (hr : ∀ i, r i ∈ Γ.R) (hrΔ : ∀ i, (r i ∩ Δ i).Nonempty)
    {q : Set S} (hq : q ∈ Γ.R) (hne : ∀ i, q ≠ r i) :
    ∃ E : Set S, IsClosedDisc E ∧ E ⊆ q ∧ Disjoint E Γ.U ∧
      Disjoint E K.U ∧ ∀ i, Disjoint E (Δ i) := by
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨x, hxq, hxK⟩ := exists_notMem_U (Γ := K) hS (region_isOpen hq) (region_nonempty hq)
  obtain ⟨E, hE, hEW⟩ := exists_closed_disc_subset_open hS
    ((region_isOpen hq).inter K.isClosed_U.isOpen_compl) ⟨x, hxq, hxK⟩
  have hEq : E ⊆ q := fun _ hx => (hEW hx).1
  refine ⟨E, hE, hEq, Set.disjoint_left.mpr (fun x hx => region_subset hq (hEq hx)),
    Set.disjoint_left.mpr (fun x hx => (hEW hx).2), ?_⟩
  intro i
  exact (region_disjoint_disc_of_ne hS (hΔ i) (havoid i) (hr i) hq (hrΔ i) (hne i)).mono_left hEq

end GraphMinor.GM12
