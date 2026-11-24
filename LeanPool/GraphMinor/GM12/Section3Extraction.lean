/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3ExtractionReduction
public import LeanPool.GraphMinor.GM12.Section3Alpha
import LeanPool.GraphMinor.GM12.Section3MeetingCircleExtraction

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# Extraction from a solid connected set

The Section 8 argument of VII used by XII (3.1), page 245, reduces a
solid connected set which is not near-planar to a schismatic subset.
The selected-circle argument handles circles, disjoint loops and loops
meeting once. The remaining intersection case follows by the proved
complete-chord homotopy reduction. Thus the only external input here
is the cited planar criterion VII (5.1).
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

universe u v

/-- Assemble the schismatic extraction used in XII (3.1) from the
proved selection cases and complete-chord intersection extraction. -/
theorem exists_schismatic_subset_of_solid
    {S : Type u} {ι : Type v} [TopologicalSpace S] [T2Space S]
    [ConnectedSpace S] [Finite ι] [Nonempty ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (hcase : ¬ IsSphere S ∨ 3 ≤ Nat.card ι)
    {X : Set (discComplement Δ)} (hX : IsSolid X) (hconn : IsConnected X)
    (hnot : ¬ GM07.IsNearPlanar X) :
    ∃ Y : Set (discComplement Δ), Y ⊆ X ∧ GM07.IsSchismatic Y := by
  rcases schismatic_extraction_or_larger_circle_intersection hS Δ hΔ hdisj
    hcase hX hconn hnot with h | ⟨F, A, i, j, hF, hA, hFX, hAX, hij, hsF, hsA, hne, hmany⟩
  · exact h
  · classical
    obtain ⟨x, hx⟩ := hne
    have hex : ∃ y ∈ F ∩ A, y ≠ x := by
      by_contra hn
      apply hmany x
      apply Subset.antisymm
      · intro y hy
        have heq : y = x := by
          by_contra hne
          exact hn ⟨y, hy, hne⟩
        exact mem_singleton_iff.mpr heq
      · exact singleton_subset_iff.mpr hx
    obtain ⟨y, hy, hyx⟩ := hex
    obtain ⟨Y, hYFA, hY⟩ := exists_schismatic_subset_of_meeting_surrounding_circles hS Δ hΔ hdisj
      hcase hij hF hA hsF hsA hx hy (Ne.symm hyx)
    exact ⟨Y, hYFA.trans (union_subset hFX hAX), hY⟩

/-- The minimum-count step of XII (3.1) after solid-set extraction.
Normality passes to the extracted subset, and its vertex count is at
most that of the original alpha candidate. The remaining inputs are
candidate existence and the bounds for
the schismatic shapes. -/
theorem alpha_ge_of_solid_extraction
    {S : Type u} {ι : Type v} [TopologicalSpace S] [T2Space S]
    [ConnectedSpace S] [Finite ι] [Nonempty ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (hcase : ¬ IsSphere S ∨ 3 ≤ Nat.card ι)
    (G : Drawing (discComplement Δ)) (N : ℕ)
    (hex : ∃ X, GM07.IsAlphaCandidate G X)
    (hbound : ∀ Y, GM07.IsSchismatic Y → G.IsNormal Y → N ≤ (Y ∩ G.V).ncard) :
    N ≤ GM07.alpha G := by
  apply alpha_ge_of_schismatic_counts G hex ?_ hbound
  intro X hX
  obtain ⟨Y, hYX, hY⟩ := exists_schismatic_subset_of_solid
    hS Δ hΔ hdisj hcase hX.1 hX.2.1 hX.2.2.2
  exact ⟨Y, hYX, hY, fun _ hy => hX.2.2.1 ⟨hYX hy.1, hy.2⟩⟩

end GraphMinor.GM12
