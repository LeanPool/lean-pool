/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM16.BoundaryNaturalOrder
import LeanPool.GraphMinor.GM11.Walks

/-!
# Boundary orders after transport

A drawing transported by an injective map draws each vertex at its
image. Transporting a circle parametrization therefore also transports
the cyclic order of its boundary vertices. These facts identify the
boundary orders in the rural presentation of XVI (8.1), Claim (11).
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11
universe u v
variable {S : Type u} {T : Type v} [TopologicalSpace S] [TopologicalSpace T]

/-- In a transported drawing each vertex is represented by its image. -/
theorem graphDrawingVertexSet_transport {D : Drawing S}
    (Γ : GraphDrawing D.toGraph T) {f : S → T}
    (hv : ∀ x : D.toGraph.vertexSet, (Γ.iso.vertexEquiv x).val = f x.val)
    {x : S} (hx : x ∈ D.V) : graphDrawingVertexSet Γ x = {f x} := by
  ext z
  change (∃ h : x ∈ D.V, (Γ.iso.vertexEquiv ⟨x, h⟩).val = z) ↔ z = f x
  constructor
  · rintro ⟨h, heq⟩
    exact heq.symm.trans (hv ⟨x, h⟩)
  · intro heq
    exact ⟨hx, (hv ⟨x, hx⟩).trans heq.symm⟩

/-- Order a nonempty finite boundary set, and carry that order through
the transported parametrization of its circle. -/
theorem exists_drawing_boundary_order {D : Drawing S}
    (Γ : GraphDrawing D.toGraph T) {f : S → T}
    (hv : ∀ x : D.toGraph.vertexSet, (Γ.iso.vertexEquiv x).val = f x.val)
    {F : Set S} {F' : Set T} (φ : Circle ≃ₜ F) (φ' : Circle ≃ₜ F')
    (hφ : ∀ z, (φ' z).val = f (φ z).val)
    (hne : (D.V ∩ F).Nonempty) :
    ∃ Ω : CyclicPerm S, Ω.bar = D.V ∩ F ∧
      DrawingAgreesWithOArcHomeo Γ Ω F' φ' := by
  obtain ⟨Ω, hbar, ha⟩ := exists_cyclicPerm_agrees φ
    (D.finite_V.inter_of_left F) hne inter_subset_right
  refine ⟨Ω, hbar, ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ D.V ∩ F := hbar ▸ hx
    rw [graphDrawingVertexSet_transport Γ hv hx'.1]
    intro z hz
    have hφx := hφ (φ.symm ⟨x, hx'.2⟩)
    have heq : f x ∈ F' := by
      rw [← show (φ (φ.symm ⟨x, hx'.2⟩)).val = x from
        congrArg Subtype.val (φ.apply_symm_apply ⟨x, hx'.2⟩), ← hφx]
      exact (φ' _).prop
    exact (mem_singleton_iff.mp hz) ▸ heq
  · intro x y z hxyz
    obtain ⟨a, b, c, hab, hbc, hca, hax, hby, hcz⟩ := ha.2 x y z hxyz
    have hx : x ∈ D.V := (hbar ▸ hxyz.2.1 x (by simp)).1
    have hy : y ∈ D.V := (hbar ▸ hxyz.2.1 y (by simp)).1
    have hz : z ∈ D.V := (hbar ▸ hxyz.2.1 z (by simp)).1
    refine ⟨a, b, c, hab, hbc, hca, ?_, ?_, ?_⟩
    · rw [graphDrawingVertexSet_transport Γ hv hx]
      exact (hφ _).trans (congrArg f hax)
    · rw [graphDrawingVertexSet_transport Γ hv hy]
      exact (hφ _).trans (congrArg f hby)
    · rw [graphDrawingVertexSet_transport Γ hv hz]
      exact (hφ _).trans (congrArg f hcz)

end GraphMinor.GM16
