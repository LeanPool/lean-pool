/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3ThirdDisc
public import LeanPool.GraphMinor.GM12.Section3PlanarityMaps
import LeanPool.GraphMinor.GM12.Section3PuncturedCuffs
import LeanPool.GraphMinor.Surface.DiscsInSurface
import LeanPool.GraphMinor.GM12.Section3DiscUniqueness

/-!
# A surrounding circle identifies its cuff

Under the surface assumption of XII (3.1), page 245, a circle cannot
surround two prescribed cuffs. The two enclosing discs have the same
boundary. They coincide by disc uniqueness, using a third deleted disc
as an outside point in the sphere case. Their exact enclosed-disc
sets identify the cuff. Consequently, a set containing circles around
distinct cuffs cannot be near-planar.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- A circle surrounds at most one prescribed cuff under the surface
condition of XII (3.1), page 245. -/
theorem surrounding_cuff_index_unique
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (hcase : ¬ IsSphere S ∨ 3 ≤ Nat.card ι)
    {i j : ι} {F : Set (discComplement Δ)} (hF : IsOArc F)
    (hsi : GM07.SurroundsCuff F (Subtype.val ⁻¹' discBd (Δ i)))
    (hsj : GM07.SurroundsCuff F (Subtype.val ⁻¹' discBd (Δ j))) : i = j := by
  classical
  obtain ⟨D, hD, hbD, hiD, hDT⟩ :=
    surrounding_bounds_disc_including_deleted_disc hS Δ hΔ hdisj i hF hsi
  obtain ⟨E, hE, hbE, hjE, hET⟩ :=
    surrounding_bounds_disc_including_deleted_disc hS Δ hΔ hdisj j hF hsj
  have hbd : discBd D = discBd E := hbD.trans hbE.symm
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have heq : D = E := by
    rcases hcase with hns | hthree
    · exact eq_of_discBd_eq ⟨hS.1, hS.2.1, hman⟩ hns hD hE hbd
    · let := Fintype.ofFinite ι
      have hthree' : 3 ≤ Fintype.card ι := by
        simpa only [Nat.card_eq_fintype_card] using hthree
      obtain ⟨k, hki, hkj⟩ := ENat.exists_ne_ne_of_three_le
        (by rw [ENat.card_eq_coe_fintype_card]; exact_mod_cast hthree') i j
      exact eq_of_discBd_eq_of_union_ne_univ hman hD hE hbd
        (union_ne_univ_of_subset_partial_fills hS Δ hΔ hki hkj hDT hET)
  have hiE : Δ i ⊆ E := heq ▸ hiD
  exact (included_disc_iff_of_subset_partial_fill hS Δ hΔ hjE hET i).mp hiE

/-- Circles surrounding distinct cuffs prevent a containing set from
being near-planar. Filling a single cuff cannot make both circles planar. -/
theorem not_isNearPlanar_of_distinct_surrounding_subcircles
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (hcase : ¬ IsSphere S ∨ 3 ≤ Nat.card ι)
    {i j : ι} (hij : i ≠ j) {F A X : Set (discComplement Δ)}
    (hF : IsOArc F) (hA : IsOArc A) (hFX : F ⊆ X) (hAX : A ⊆ X)
    (hsi : GM07.SurroundsCuff F (Subtype.val ⁻¹' discBd (Δ i)))
    (hsj : GM07.SurroundsCuff A (Subtype.val ⁻¹' discBd (Δ j))) :
    ¬ GM07.IsNearPlanar X := by
  intro hnear
  rcases hnear with hp | ⟨C, hC, hpC⟩
  · exact hsi.2.2 (isPlanar_mono hFX hp)
  · have hC' := hC
    rw [discComplement_cuffs_eq hS Δ hΔ hdisj] at hC'
    obtain ⟨k, rfl⟩ := hC'
    have hsFk : GM07.SurroundsCuff F (Subtype.val ⁻¹' discBd (Δ k)) :=
      ⟨hC, isPlanarInCappedCuff_mono hFX hpC, hsi.2.2⟩
    have hsAk : GM07.SurroundsCuff A (Subtype.val ⁻¹' discBd (Δ k)) :=
      ⟨hC, isPlanarInCappedCuff_mono hAX hpC, hsj.2.2⟩
    have hik := surrounding_cuff_index_unique hS Δ hΔ hdisj hcase hF hsi hsFk
    have hjk := surrounding_cuff_index_unique hS Δ hΔ hdisj hcase hA hsj hsAk
    exact hij (hik.trans hjk.symm)

end GraphMinor.GM12
