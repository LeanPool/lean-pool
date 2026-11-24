/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4EndPartition
public import LeanPool.GraphMinor.Surface.PlaneDisc

/-!
# Transporting contact partitions between homeomorphic spaces

The small-surface reduction for XII (4.5) must retain its
vertex-disc witnesses and exact endpoint classes. A homeomorphism
carries discs and disjointness to their images, and its image
commutes with intersections and unions. The class of image ends
is the image of the old end class. Boundary parametrizations
transport by composition with the same homeomorphism.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- A homeomorphism transports disjoint contact discs and their
exact end classes, in arbitrary universes. This carries the
small-surface construction of XII (4.5) back to the surface. -/
theorem contact_partition_image {S T V E I : Type*} [TopologicalSpace S] [TopologicalSpace T]
    (e : S ≃ₜ T) (B : V → Set S) (C : I → Set S) (ends : E → S) (κ : E → V)
    (hB : ∀ w, IsClosedDisc (B w)) (hBB : Pairwise (fun w z => Disjoint (B w) (B z)))
    (hcontact : ∀ w, B w ∩ (⋃ i, C i) = edgeEndClass ends κ w) :
    (∀ w, IsClosedDisc (e '' B w)) ∧
      Pairwise (fun w z => Disjoint (e '' B w) (e '' B z)) ∧
      ∀ w, (e '' B w) ∩ (⋃ i, e '' C i) = edgeEndClass (e ∘ ends) κ w := by
  have hclass : ∀ w, e '' edgeEndClass ends κ w = edgeEndClass (e ∘ ends) κ w := by
    intro w
    simp only [edgeEndClass, image_image]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro w
    exact ((hB w).image e.continuous.continuousOn e.symm.continuous.continuousOn
      (fun z _ => e.symm_apply_apply z)).1
  · intro w z hwz
    exact (disjoint_image_iff e.injective).mpr (hBB hwz)
  · intro w
    rw [← image_iUnion, ← image_inter e.injective, hcontact w, hclass w]

/-- A boundary parametrization transports through a homeomorphism,
including its whole boundary image equation. -/
theorem boundary_param_image_homeomorph {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    (e : S ≃ₜ T) {D : Set S} (hD : IsClosedDisc D) (p : Circle → S)
    (hp : Continuous p ∧ Function.Injective p ∧ range p = discBd D) :
    Continuous (e ∘ p) ∧ Function.Injective (e ∘ p) ∧ range (e ∘ p) = discBd (e '' D) := by
  have hb := (hD.image e.continuous.continuousOn e.symm.continuous.continuousOn
    (fun z _ => e.symm_apply_apply z)).2
  refine ⟨e.continuous.comp hp.1, e.injective.comp hp.2.1, ?_⟩
  rw [range_comp, hp.2.2, hb]

end GraphMinor.GM12
