/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.Surface.Crossing
import LeanPool.GraphMinor.Surface.Jordan
import LeanPool.GraphMinor.Surface.PlaneSeparation

/-!
# Two facts on the plane, and closed surfaces are surfaces

Graph Minors XI says that a drawing without circuits in a connected surface has only one region.
Our proof of that fact, in `GraphMinor/GM11/ForestRegions.lean`, uses two classical facts on the
plane: an arc does not separate the plane, and Janiszewski's theorem. Both are proved over `ℂ` in
`GraphMinor/Surface/PlaneSeparation.lean` and `GraphMinor/Surface/Crossing.lean`. This file carries
them over the isometry `complexPlane` to `EuclideanPlane`, as `isPreconnected_compl_of_isLine` and
`janiszewski_plane`.

It also proves `IsClosedSurface.isSurface`: a compact 2-manifold without boundary is a compact
2-manifold with (possibly null) boundary. An open disc embeds as an open subset of the half plane by
a translation.
-/

public section

namespace GraphMinor.Surface

open Set Topology

universe u

/-- The homeomorphism between `ℂ` and the plane. -/
private noncomputable def complexPlaneHomeo : ℂ ≃ₜ EuclideanPlane := complexPlane.toHomeomorph

/-- A homeomorphism carries the components of a complement to the components of the complement of
the image. -/
private theorem image_component (A : Set ℂ) {a : ℂ} (ha : a ∈ Aᶜ) :
    complexPlaneHomeo '' connectedComponentIn Aᶜ a =
      connectedComponentIn (complexPlaneHomeo '' A)ᶜ (complexPlaneHomeo a) := by
  rw [complexPlaneHomeo.image_connectedComponentIn ha, image_compl_eq complexPlaneHomeo.bijective]

/-- The set of `ℂ` that corresponds to a set of the plane. -/
private theorem image_symm (A : Set EuclideanPlane) :
    complexPlaneHomeo '' (complexPlaneHomeo.symm '' A) = A := by
  rw [← image_comp]
  simp

/-- An arc does not separate the plane. Follows from `component_eq_of_arc`. -/
theorem isPreconnected_compl_of_isLine {L : Set EuclideanPlane} (hL : IsLine L) :
    IsPreconnected Lᶜ := by
  obtain ⟨φ⟩ := hL
  set L' : Set ℂ := complexPlaneHomeo.symm '' L with hL'
  have φ' : unitInterval ≃ₜ L' := φ.trans (complexPlaneHomeo.symm.image L)
  have hcomp : ∀ a b : EuclideanPlane, a ∈ Lᶜ → b ∈ Lᶜ → b ∈ connectedComponentIn Lᶜ a := by
    intro a b ha hb
    have ha' : complexPlaneHomeo.symm a ∉ L' := by
      rintro ⟨x, hx, h⟩
      rw [complexPlaneHomeo.symm.injective h] at hx
      exact ha hx
    have hb' : complexPlaneHomeo.symm b ∉ L' := by
      rintro ⟨x, hx, h⟩
      rw [complexPlaneHomeo.symm.injective h] at hx
      exact hb hx
    have heq := component_eq_of_arc φ' ha' hb'
    have hmem : complexPlaneHomeo.symm b ∈ connectedComponentIn L'ᶜ (complexPlaneHomeo.symm a) := by
      rw [heq]
      exact mem_connectedComponentIn hb'
    have himg := mem_image_of_mem complexPlaneHomeo hmem
    rw [image_component _ ha', hL', image_symm] at himg
    simpa using himg
  refine isPreconnected_of_forall_pair fun a ha b hb => ?_
  exact ⟨connectedComponentIn Lᶜ a, connectedComponentIn_subset _ _,
    mem_connectedComponentIn ha, hcomp a b ha hb, isPreconnected_connectedComponentIn⟩

/-- **Janiszewski's theorem**, in the plane. If `A ∩ B` is preconnected, and neither of the compact
sets `A`, `B` separates `x` from `y`, then `A ∪ B` does not separate them. Follows from
`janiszewski`. -/
theorem janiszewski_plane {A B : Set EuclideanPlane} (hA : IsCompact A) (hB : IsCompact B)
    (hAB : IsPreconnected (A ∩ B)) {x y : EuclideanPlane} (hx : x ∉ A ∪ B) (hy : y ∉ A ∪ B)
    (h₁ : y ∈ connectedComponentIn Aᶜ x) (h₂ : y ∈ connectedComponentIn Bᶜ x) :
    y ∈ connectedComponentIn (A ∪ B)ᶜ x := by
  let f := complexPlaneHomeo.symm
  have hn : ∀ {C : Set EuclideanPlane} {z : EuclideanPlane}, z ∉ C → f z ∉ f '' C := by
    rintro C z hz ⟨w, hw, h⟩
    rw [f.injective h] at hw
    exact hz hw
  have comp : ∀ {C : Set EuclideanPlane}, y ∈ connectedComponentIn Cᶜ x → x ∉ C →
      f y ∈ connectedComponentIn (f '' C)ᶜ (f x) := by
    intro C h hxC
    have hm := mem_image_of_mem f h
    rw [f.image_connectedComponentIn hxC, image_compl_eq f.bijective] at hm
    exact hm
  have hxA : x ∉ A := fun h => hx (Or.inl h)
  have hxB : x ∉ B := fun h => hx (Or.inr h)
  have hmem := janiszewski (K₁ := f '' A) (K₂ := f '' B) (hA.image f.continuous)
    (hB.image f.continuous)
    (by rw [← image_inter f.injective]; exact hAB.image _ f.continuous.continuousOn)
    (by rw [← image_union]; exact hn hx) (by rw [← image_union]; exact hn hy)
    (comp h₁ hxA) (comp h₂ hxB)
  rw [← image_union] at hmem
  have him := mem_image_of_mem complexPlaneHomeo hmem
  have hmemc : f x ∈ (f '' (A ∪ B))ᶜ := hn hx
  rw [image_component _ hmemc] at him
  have himg : complexPlaneHomeo '' (f '' (A ∪ B)) = A ∪ B := image_symm _
  rw [himg] at him
  simpa [f] using him

/-- A point of the plane with positive first coordinate. -/
private noncomputable def shift : EuclideanPlane := EuclideanSpace.single 0 2

/-- The translation of the open unit disc into the half plane. -/
private noncomputable def discToHalf (x : OpenUnitDisc) : EuclideanHalfSpace 2 :=
  ⟨x.1 + shift, by
    have h1 : ‖x.1‖ < 1 := mem_ball_zero_iff.mp x.2
    have h2 : |x.1 0| ≤ ‖x.1‖ := by
      simpa using PiLp.norm_apply_le x.1 0
    have h3 := (abs_lt.mp (lt_of_le_of_lt h2 h1)).1
    simp only [PiLp.add_apply, shift, PiLp.single_apply, ite_true]
    linarith⟩

private theorem isEmbedding_discToHalf : IsEmbedding discToHalf := by
  have h : IsEmbedding (Subtype.val ∘ discToHalf) := by
    have : (Subtype.val ∘ discToHalf) = (Homeomorph.addRight shift) ∘ Subtype.val := rfl
    rw [this]
    exact (Homeomorph.addRight shift).isEmbedding.comp IsEmbedding.subtypeVal
  exact IsEmbedding.of_comp (by unfold discToHalf; fun_prop) continuous_subtype_val h

private theorem isOpen_range_discToHalf : IsOpen (range discToHalf) := by
  have : range discToHalf = Subtype.val ⁻¹' ((fun y => y - shift) ⁻¹' Metric.ball 0 1) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      have hx : ‖x.1‖ < 1 := mem_ball_zero_iff.mp x.2
      simpa [discToHalf] using hx
    · intro hy
      exact ⟨⟨y.1 - shift, hy⟩, Subtype.ext (sub_add_cancel _ _)⟩
  rw [this]
  exact (Metric.isOpen_ball.preimage (by fun_prop)).preimage continuous_subtype_val

/-- An interior point is a manifold point: an open disc embeds as an open subset of the half
plane. -/
theorem IsInteriorPoint.isManifoldPoint {S : Type u} [TopologicalSpace S] {x : S}
    (h : IsInteriorPoint x) : IsManifoldPoint x := by
  obtain ⟨U, hU, hx, ⟨e⟩⟩ := h
  exact ⟨U, range discToHalf, hU, isOpen_range_discToHalf, hx,
    ⟨e.trans isEmbedding_discToHalf.toHomeomorph⟩⟩

/-- A compact 2-manifold without boundary (the surfaces of Graph Minors XI) is a compact 2-manifold
with possibly null boundary (the surfaces of Graph Minors VII). -/
theorem IsClosedSurface.isSurface {S : Type u} [TopologicalSpace S] (h : IsClosedSurface S) :
    IsSurface S :=
  ⟨h.1, h.2.1, fun x => (h.2.2 x).isManifoldPoint⟩

end GraphMinor.Surface
