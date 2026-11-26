/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Collar
import LeanPool.GraphMinor.GM12.Section4DiscMatch
import LeanPool.GraphMinor.GM12.Section4DiscCompression
import LeanPool.GraphMinor.GM12.Section4DiscEnlargement
import LeanPool.GraphMinor.GM12.Section4ProtectedMotion
import LeanPool.GraphMinor.GM11.Section6
import LeanPool.GraphMinor.Surface.Wedge

/-!
# Matching one disc while fixing protected discs

For XII (4.3), claim (7), page 251, match discs one at a time.
Move a compression center of the source into the target's interior.
Compress the source before this motion so its image lies inside the
target. The nested-disc homeomorphism then expands that image onto
the target. Each motion fixes the protected discs pointwise.
-/

public section

namespace GraphMinor.GM12

open Set Surface Metric GM11

/-- Match two closed discs outside a protected disjoint disc family,
fixing every protected disc pointwise. -/
theorem exists_disc_match_fixing_discs
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [Finite ι]
    (hS : IsClosedSurface S) (D : ι → Set S) (hD : ∀ i, IsClosedDisc (D i))
    (hDD : Pairwise (fun i j => Disjoint (D i) (D j)))
    {A B : Set S} (hA : IsClosedDisc A) (hB : IsClosedDisc B)
    (hAD : Disjoint A (⋃ i, D i)) (hBD : Disjoint B (⋃ i, D i)) :
    ∃ e : S ≃ₜ S, e '' A = B ∧ ∀ i z, z ∈ D i → e z = z := by
  let Z := ⋃ i, D i
  have hZ : IsClosed Z := isClosed_iUnion_of_finite fun i => (hD i).isClosed
  obtain ⟨p, hpA, hcompress⟩ := exists_disc_compression_center hS hA hZ hAD
  obtain ⟨h, g, c⟩ := hB.exists_isChart
  have hBi : discInt B = interior B := by
    rw [discInt, ← IsClosedDisc.frontier_eq_discBd hS hB, self_sdiff_frontier]
  have hq : g 0 ∈ interior B := by
    rw [← hBi, c.discInt_eq]
    exact mem_image_of_mem g (by simp)
  have hpZ : p ∉ ⋃ i, D i := Set.disjoint_left.mp hAD hpA
  have hqZ : g 0 ∉ ⋃ i, D i := Set.disjoint_left.mp hBD (interior_subset hq)
  obtain ⟨f, hfp, hffix⟩ := exists_point_motion_fixing_discs hS D hD hDD hpZ hqZ
  let U := f ⁻¹' interior B
  have hU : IsOpen U := isOpen_interior.preimage f.continuous
  have hpU : p ∈ U := by change f p ∈ interior B; rw [hfp]; exact hq
  obtain ⟨s, hsA, _, hsfix⟩ := hcompress U hU hpU
  let H := s.trans f
  have hHA : H '' A ⊆ interior B := by
    rintro _ ⟨x, hxA, rfl⟩
    exact hsA (mem_image_of_mem s hxA)
  have hHfix : ∀ i z, z ∈ D i → H z = z := by
    intro i z hz
    change f (s z) = z
    rw [hsfix z (mem_iUnion.mpr ⟨i, hz⟩), hffix i z hz]
  have hnonempty : Nonempty S := ⟨p⟩
  have hHA_disc : IsClosedDisc (H '' A) :=
    (isClosedDisc_image_injOn hA hA.isCompact H.continuous.continuousOn H.injective.injOn).1
  obtain ⟨E, hE, hBE, hEZ⟩ := exists_disc_enlargement_avoiding hS hB hZ hBD
  have hHAB : H '' A ⊆ B \ discBd B := by
    rw [← discInt, hBi]
    exact hHA
  obtain ⟨k, hkA, hkfix⟩ := exists_disc_onto_nested
    (fun x => (hS.2.2 x).isManifoldPoint) hHA_disc hB hE hHAB hBE
  refine ⟨H.trans k, ?_, ?_⟩
  · change (fun x => k (H x)) '' A = B
    simpa only [image_image] using hkA
  · intro i z hz
    change k (H z) = z
    rw [hHfix i z hz]
    exact hkfix z (fun hzE => Set.disjoint_left.mp hEZ hzE (mem_iUnion.mpr ⟨i, hz⟩))

end GraphMinor.GM12
