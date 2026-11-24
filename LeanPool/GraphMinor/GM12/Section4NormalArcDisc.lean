/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CrossCut
import LeanPool.GraphMinor.GM12.Section4ThinArcDisc
import LeanPool.GraphMinor.Surface.Classification
import LeanPool.GraphMinor.Surface.InvarianceOfDomain
import LeanPool.GraphMinor.Surface.Wedge

/-!
# Empty discs in closed connected surfaces

The thin-disc construction for XII (4.3), page 250, is invariant
under homeomorphisms. Apply it on a model of the surface and carry
its disc back. This permits arbitrary universes for the original
surface while the plane and arc-chart construction uses its usual
small model.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- The thin-disc construction used in XII (4.3), page 250, for
a closed connected surface in an arbitrary universe. -/
theorem exists_normal_arc_disc
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {a : unitInterval → S} (ha : IsArcMap a)
    {B : Set S} (hB : IsClosed B) (hleft : a 0 ∈ B) (hright : a 1 ∈ B)
    (hmeet : range a ∩ B ⊆ {a 0, a 1}) :
    ∃ D : Set S, IsClosedDisc D ∧ D ∩ B = {a 0, a 1} ∧
      ({a 0, a 1} : Set S) ⊆ discBd D ∧ range a ⊆ D := by
  let : CompactSpace S := hS.1
  have hsurf : IsSurface S := ⟨hS.1, hS.2.1, fun x => (hS.2.2 x).isManifoldPoint⟩
  obtain ⟨n, m, c, ⟨e⟩⟩ := classification S hsurf inferInstance
  let : T2Space (SurfaceModel n m c) := e.t2Space
  have hM : IsClosedSurface (SurfaceModel n m c) := by
    refine ⟨e.compactSpace, e.t2Space, ?_⟩
    intro x
    have hx := (isInteriorPoint_homeomorph_iff e (e.symm x)).mpr (hS.2.2 (e.symm x))
    simpa only [e.apply_symm_apply] using hx
  let a' : unitInterval → SurfaceModel n m c := fun t => e (a t)
  let B' : Set (SurfaceModel n m c) := e.symm ⁻¹' B
  have ha' : IsArcMap a' := ⟨e.continuous.comp ha.1, e.injective.comp ha.2⟩
  have hB' : IsClosed B' := hB.preimage e.symm.continuous
  have hleft' : a' 0 ∈ B' := by simpa only [a', B', mem_preimage, e.symm_apply_apply] using hleft
  have hright' : a' 1 ∈ B' := by simpa only [a', B', mem_preimage, e.symm_apply_apply] using hright
  have hmeet' : range a' ∩ B' ⊆ {a' 0, a' 1} := by
    rintro _ ⟨⟨t, rfl⟩, ht⟩
    have htB : a t ∈ B := by simpa only [a', B', mem_preimage, e.symm_apply_apply] using ht
    rcases hmeet ⟨mem_range_self t, htB⟩ with h | h
    · exact Or.inl (congrArg e h)
    · exact Or.inr (Set.mem_singleton_iff.mpr (congrArg e (Set.mem_singleton_iff.mp h)))
  obtain ⟨D, hD, hDB, hends, haD⟩ := exists_thin_disc_of_arc hM ha' hB' hleft' hright' hmeet'
  let : Nonempty (SurfaceModel n m c) := ⟨a' 0⟩
  have himage := isClosedDisc_image_injOn hD hD.isCompact e.symm.continuous.continuousOn
    e.symm.injective.injOn
  refine ⟨e.symm '' D, himage.1, ?_, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · rintro _ ⟨⟨x, hx, rfl⟩, hxB⟩
      have hxends : x ∈ ({a' 0, a' 1} : Set (SurfaceModel n m c)) := hDB.subset ⟨hx, hxB⟩
      rcases hxends with rfl | hxends
      · exact Or.inl (e.symm_apply_apply (a 0))
      · have hx1 := Set.mem_singleton_iff.mp hxends
        subst x
        exact Or.inr (Set.mem_singleton_iff.mpr (e.symm_apply_apply (a 1)))
    · intro x hx
      rcases hx with rfl | hx
      · exact ⟨⟨a' 0, discBd_subset D (hends (by simp)), e.symm_apply_apply (a 0)⟩, hleft⟩
      · have hx1 := Set.mem_singleton_iff.mp hx
        subst x
        exact ⟨⟨a' 1, discBd_subset D (hends (by simp)), e.symm_apply_apply (a 1)⟩, hright⟩
  · rw [himage.2]
    intro x hx
    rcases hx with rfl | hx
    · exact ⟨a' 0, hends (by simp), e.symm_apply_apply (a 0)⟩
    · have hx1 := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨a' 1, hends (by simp), e.symm_apply_apply (a 1)⟩
  · rintro _ ⟨t, rfl⟩
    exact ⟨a' t, haD (mem_range_self t), e.symm_apply_apply (a t)⟩

end GraphMinor.GM12
