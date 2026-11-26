/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3SubcircleSelection
public import LeanPool.GraphMinor.GM12.Section3CircleSchismatic
public import LeanPool.GraphMinor.GM12.Section3Punctured
import LeanPool.GraphMinor.GM12.Section3BarbellSchismatic
import LeanPool.GraphMinor.GM12.Section3MeetingLoopSchismatic
import LeanPool.GraphMinor.GM12.Section3PuncturedCuffs
import LeanPool.GraphMinor.GM12.Section3PuncturedSurface

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# The remaining intersection case in schismatic extraction

The Section 8 reduction used by XII (3.1), page 245, selects either
a circle which is not near-planar or circles surrounding distinct cuffs.
The circle, disjoint-circle and single-intersection cases now yield
schismatic subsets. This theorem assembles those proved cases and
leaves precisely the case of two selected circles with a larger
intersection, which must be reduced to the three-branch shape or a
new circle.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

universe u

/-- Reduction of the Section 8 extraction argument to selected
surrounding circles whose intersection is neither empty nor one point.
Every other selection case supplies a schismatic subset. -/
theorem schismatic_extraction_or_larger_circle_intersection
    {S : Type u} {ι : Type*} [TopologicalSpace S] [T2Space S]
    [ConnectedSpace S] [Finite ι] [Nonempty ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (hcase : ¬ IsSphere S ∨ 3 ≤ Nat.card ι)
    {X : Set (discComplement Δ)} (hX : IsSolid X) (hconn : IsConnected X)
    (hnot : ¬ GM07.IsNearPlanar X) :
    (∃ Y : Set (discComplement Δ), Y ⊆ X ∧ GM07.IsSchismatic Y) ∨
      ∃ (F A : Set (discComplement Δ)) (i j : ι),
        IsOArc F ∧ IsOArc A ∧ F ⊆ X ∧ A ⊆ X ∧ i ≠ j ∧
        GM07.SurroundsCuff F (Subtype.val ⁻¹' discBd (Δ i)) ∧
        GM07.SurroundsCuff A (Subtype.val ⁻¹' discBd (Δ j)) ∧
        (F ∩ A).Nonempty ∧ ∀ u, F ∩ A ≠ {u} := by
  classical
  let : ConnectedSpace (discComplement Δ) :=
    Subtype.connectedSpace (discComplement_isConnected hS Δ hΔ hdisj)
  have hsurface := discComplement_isSurface hS Δ hΔ hdisj
  have hcuff := discComplement_cuffs_nonempty hS Δ hΔ hdisj
  rcases exists_non_nearplanar_circle_or_distinct_surrounding_circles hsurface hcuff hX hnot with
    ⟨F, hF, hFX, hnotF⟩ | ⟨F, A, C, C', hF, hA, hFX, hAX, hC, hC', hCC', hsF, hsA⟩
  · exact Or.inl ⟨F, hFX, isSchismatic_oArc hF hnotF⟩
  · have hCi : C ∈ cuffs (discComplement Δ) := hC
    rw [discComplement_cuffs_eq hS Δ hΔ hdisj] at hCi
    obtain ⟨i, rfl⟩ := hCi
    have hCj : C' ∈ cuffs (discComplement Δ) := hC'
    rw [discComplement_cuffs_eq hS Δ hΔ hdisj] at hCj
    obtain ⟨j, rfl⟩ := hCj
    have hij : i ≠ j := by
      intro he
      apply hCC'
      rw [he]
    by_cases hdis : Disjoint F A
    · exact Or.inl (exists_schismatic_x1_of_disjoint_surrounding_subcircles
        hS Δ hΔ hdisj hcase hX hconn hij hF hA hFX hAX hdis hsF hsA)
    · by_cases hpoint : ∃ u, F ∩ A = {u}
      · obtain ⟨u, hu⟩ := hpoint
        exact Or.inl (exists_schismatic_x2_of_meeting_surrounding_subcircles
          hS Δ hΔ hdisj hcase hij hF hA hFX hAX hu hsF hsA)
      · have hne : (F ∩ A).Nonempty := by
          by_contra hn
          exact hdis (Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hn))
        exact Or.inr ⟨F, A, i, j, hF, hA, hFX, hAX, hij, hsF, hsA, hne,
          fun u hu => hpoint ⟨u, hu⟩⟩

end GraphMinor.GM12
