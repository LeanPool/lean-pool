/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section72LocalDiversion

/-!
# Diverting a normal circle off a disc through one vertex

This proves the geometric diversion in XII (7.2), page 260. If the
circle misses the vertex, push it off the disc directly. Otherwise,
the local corner-cap argument first separates it from the boundary
circle near the vertex. One short boundary half-line then meets the
circle only at the vertex. A final disc push removes all other
intersections with the disc, fixing the outside drawing throughout.
-/

public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- The diversion in XII (7.2), page 260. For a non-isolated boundary
vertex, a normal circle can be moved off the disc except at that vertex,
by a homeomorphism fixing the drawing pointwise. -/
theorem theorem_7_2_divert (hS : IsClosedSurface S)
    {Γ : Drawing S} {Δ C : Set S} {v : S}
    (hΔ : IsClosedDisc Δ) (hvb : v ∈ discBd Δ) (hv : v ∈ Γ.V)
    (hGD : Γ.U ∩ Δ ⊆ {v}) (hC : IsOArc C)
    (hn : (PaintingOrDrawing.drawing Γ).IsNormal C)
    (hincident : ∃ e ∈ Γ.E, v ∈ closure e) :
    ∃ h : S ≃ₜ S, (∀ x ∈ Γ.U, h x = x) ∧ (h '' C) ∩ Δ ⊆ {v} := by
  have hCc : IsClosed C := by
    obtain ⟨e⟩ := hC
    have : CompactSpace C := e.compactSpace
    exact (isCompact_iff_compactSpace.mpr this).isClosed
  by_cases hvC : v ∈ C
  swap
  · obtain ⟨h, hfix, hdis⟩ := theorem_7_2_push_away_of_notMem hS hΔ hvb Γ.isClosed_U hGD hC hvC
    exact ⟨h, hfix, fun x hx => (disjoint_left.mp hdis hx.1 hx.2).elim⟩
  have hFb : IsClosed (discBd Δ) := by
    rw [← IsClosedDisc.frontier_eq_discBd hS hΔ]
    exact isClosed_frontier
  have hFG : discBd Δ ∩ Γ.U ⊆ {v} :=
    fun x hx => hGD ⟨hx.2, Surface.discBd_subset Δ hx.1⟩
  obtain ⟨h, N, hNo, hvN, hfix, hlocal⟩ :=
    exists_local_circle_diversion hS hC hn hv hvC hincident hFb hFG
  let C' := h.symm '' C
  let N' := h ⁻¹' N
  have hN'o : IsOpen N' := hNo.preimage h.continuous
  have hvN' : v ∈ N' := by
    change h v ∈ N
    rwa [hfix v (Γ.V_subset_U hv)]
  have hlocal' : (discBd Δ ∩ C') ∩ N' ⊆ {v} := by
    rintro x ⟨⟨hxb, hxC⟩, hxN⟩
    have hxC' : h x ∈ C := by
      change x ∈ h.symm '' C at hxC
      rwa [h.image_symm] at hxC
    have hxv : h x = v := mem_singleton_iff.mp
      (hlocal ⟨⟨mem_image_of_mem h hxb, hxC'⟩, hxN⟩)
    exact mem_singleton_iff.mpr (h.injective (hxv.trans (hfix v (Γ.V_subset_U hv)).symm))
  obtain ⟨L, a, b, hL, hLb, hvL, hLN, ha, hb, _⟩ :=
    exists_small_boundary_line hΔ.isOArc_discBd hvb hN'o.isClosed_compl (not_not.mpr hvN')
  have hLN' : L ⊆ N' := fun x hx => by
    by_contra hxn
    exact disjoint_left.mp hLN hx hxn
  obtain ⟨A, B, hA', _, hAB, _⟩ := hL.split hvL ha.symm hb.symm
  have hA : IsLineWithEnds A v a := Surface.IsLineWithEnds.symm hA'
  have hAL : A ⊆ L := subset_union_left.trans hAB.subset
  have hAb : A ⊆ discBd Δ := hAL.trans hLb
  have hvA : v ∈ A := by obtain ⟨e, h0, _⟩ := hA; exact h0 ▸ (e 0).2
  have haA : a ∈ A := by obtain ⟨e, _, h1⟩ := hA; exact h1 ▸ (e 1).2
  have hGA : (Γ.U ∪ {a}) ∩ Δ ⊆ A := by
    rintro x ⟨hxG | hxa, hxΔ⟩
    · exact (mem_singleton_iff.mp (hGD ⟨hxG, hxΔ⟩)).symm ▸ hvA
    · exact (mem_singleton_iff.mp hxa).symm ▸ haA
  have hC'A : C' ∩ A ⊆ {v} := by
    rintro x ⟨hxC, hxA⟩
    exact hlocal' ⟨⟨hAb hxA, hxC⟩, hLN' (hAL hxA)⟩
  have hC'c : IsClosed C' := h.symm.isClosedMap _ hCc
  obtain ⟨k, kfix, kpush⟩ := push_cap_fixing hS hΔ hA ha hAb
    (Γ.isClosed_U.union isClosed_singleton) (Or.inl (Γ.V_subset_U hv))
    (Or.inr rfl) hGA hC'c hC'A
  let f := h.symm.trans k
  refine ⟨f, ?_, ?_⟩
  · intro x hx
    have hh : h.symm x = x := by
      rw [h.symm_apply_eq]
      exact (hfix x hx).symm
    change k (h.symm x) = x
    rw [hh]
    exact kfix x (Or.inl hx)
  · rintro x ⟨⟨y, hy, hyx⟩, hxΔ⟩
    exact kpush ⟨⟨h.symm y, ⟨y, hy, rfl⟩, hyx⟩, hxΔ⟩

end GraphMinor.GM12
