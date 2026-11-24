/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Collar
import LeanPool.GraphMinor.GM12.Section4ProtectedDiscMatch
import LeanPool.GraphMinor.GM12.Section4DiscMatch
import LeanPool.GraphMinor.GM12.Section4DiscTwist
import LeanPool.GraphMinor.GM12.Section4DiscEnlargement
import LeanPool.GraphMinor.Surface.Wedge

/-!
# Matching a disc with two boundary marks

XII (4.3), claim (7), page 251, requires the orientation of each
residual edge to be preserved. First match the whole disc while
fixing the previously placed discs. A circle homeomorphism sends
the two resulting boundary points to the assigned ordered pair.
Its collar extension supplies the boundary adjustment.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Match two ordered pairs of distinct boundary points as well as
their discs, fixing a disjoint protected disc family pointwise. -/
theorem exists_marked_disc_match_fixing_discs
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [Finite ι]
    (hS : IsClosedSurface S) (D : ι → Set S) (hD : ∀ i, IsClosedDisc (D i))
    (hDD : Pairwise (fun i j => Disjoint (D i) (D j)))
    {A B : Set S} (hA : IsClosedDisc A) (hB : IsClosedDisc B)
    (hAD : Disjoint A (⋃ i, D i)) (hBD : Disjoint B (⋃ i, D i))
    {a b a' b' : S} (ha : a ∈ discBd A) (hb : b ∈ discBd A) (hab : a ≠ b)
    (ha' : a' ∈ discBd B) (hb' : b' ∈ discBd B) (hab' : a' ≠ b') :
    ∃ e : S ≃ₜ S, e '' A = B ∧ e a = a' ∧ e b = b' ∧
      ∀ i z, z ∈ D i → e z = z := by
  obtain ⟨f, hfA, hffix⟩ := exists_disc_match_fixing_discs hS D hD hDD hA hB hAD hBD
  have hnonempty : Nonempty S := ⟨a⟩
  have hfbd := (isClosedDisc_image_injOn hA hA.isCompact f.continuous.continuousOn
    f.injective.injOn).2
  rw [hfA] at hfbd
  have hfa : f a ∈ discBd B := hfbd ▸ mem_image_of_mem f ha
  have hfb : f b ∈ discBd B := hfbd ▸ mem_image_of_mem f hb
  obtain ⟨p⟩ := hB.isOArc_discBd
  let x := p.symm ⟨f a, hfa⟩
  let y := p.symm ⟨f b, hfb⟩
  let x' := p.symm ⟨a', ha'⟩
  let y' := p.symm ⟨b', hb'⟩
  have hxy : x ≠ y := by
    intro h
    exact hab (f.injective (congrArg Subtype.val (p.symm.injective h)))
  have hxy' : x' ≠ y' := by
    intro h
    exact hab' (congrArg Subtype.val (p.symm.injective h))
  obtain ⟨q, hq, hqx, hqy⟩ := exists_circle_pair_move hxy hxy'
  have hZ : IsClosed (⋃ i, D i) := isClosed_iUnion_of_finite fun i => (hD i).isClosed
  obtain ⟨E, hE, hBE, hEZ⟩ := exists_disc_enlargement_avoiding hS hB hZ hBD
  obtain ⟨k, hkB, hkmarks, hkfix⟩ := exists_boundary_twist
    (fun z => (hS.2.2 z).isManifoldPoint) hB hE hBE p hq
  have hkfa : k (f a) = a' := by
    have h := hkmarks x
    rw [hqx] at h
    simpa only [x, x', p.apply_symm_apply] using h
  have hkfb : k (f b) = b' := by
    have h := hkmarks y
    rw [hqy] at h
    simpa only [y, y', p.apply_symm_apply] using h
  refine ⟨f.trans k, ?_, hkfa, hkfb, ?_⟩
  · change (fun x => k (f x)) '' A = B
    have h := congrArg (fun C => k '' C) hfA
    simpa only [image_image, hkB] using h
  · intro i z hz
    change k (f z) = z
    rw [hffix i z hz]
    exact hkfix z (fun hzE => Set.disjoint_left.mp hEZ hzE (mem_iUnion.mpr ⟨i, hz⟩))

end GraphMinor.GM12
