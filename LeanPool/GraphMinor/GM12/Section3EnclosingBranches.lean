/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3PartialPlanarity
public import LeanPool.GraphMinor.GM12.Section3SurroundingDisc

/-!
# Enclosing discs exclude the opposite branch

For XII (3.1)(iv), page 245, each pair of branches surrounds one cuff.
Its enclosing disc cannot also contain the opposite branch: then the
whole set would be planar in that partial fill and therefore near-planar.
The argument works for any decomposition into a surrounding circle and
its complementary part.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- The enclosing discs for surrounding circles exclude the
complementary parts of a set which is not near-planar. This supplies
the opposite-branch condition in XII (3.1)(iv). -/
theorem exists_enclosing_discs_excluding_complementary_parts
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    {X : Set (discComplement Δ)} (P Q : ι → Set (discComplement Δ))
    (hcover : ∀ i, Q i ∪ P i = X)
    (hQ : ∀ i, IsOArc (Q i))
    (hs : ∀ i, GM07.SurroundsCuff (Q i) (Subtype.val ⁻¹' discBd (Δ i)))
    (hnot : ¬ GM07.IsNearPlanar X) :
    ∃ D : ι → Set S, ∀ i, IsClosedDisc (D i) ∧
      discBd (D i) = (Subtype.val : discComplement Δ → S) '' Q i ∧
      Δ i ⊆ D i ∧ ¬ (Subtype.val : discComplement Δ → S) '' P i ⊆ D i := by
  classical
  choose D hD hbd hinc hDT using fun i =>
    surrounding_bounds_disc_including_deleted_disc hS Δ hΔ hdisj i (hQ i) (hs i)
  refine ⟨D, fun i => ⟨hD i, hbd i, hinc i, ?_⟩⟩
  intro hP
  apply hnot
  apply isNearPlanar_of_image_subset_disc_in_partial_fill hS Δ hΔ hdisj i (hD i) (hDT i)
  rw [← hcover i, image_union]
  apply union_subset _ hP
  rw [← hbd i]
  exact discBd_subset (D i)

end GraphMinor.GM12
