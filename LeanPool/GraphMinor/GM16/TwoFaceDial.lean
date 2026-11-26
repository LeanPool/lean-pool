/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs
import LeanPool.GraphMinor.GM16.FaceSubdisc
import LeanPool.GraphMinor.GM16.LineDial
import LeanPool.GraphMinor.GM11.Section7
import LeanPool.GraphMinor.GM11.Section6
import LeanPool.GraphMinor.Surface.DiscUnion
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# Gluing the two halves of a dial

A circle with one line in each of two empty faces cuts off a disc
in each face. Each disc meets the drawing in the same boundary
subline. Glue the discs along that line. The glued boundary is the
original circle, and its intersection with the drawing is a line,
so its restricted drawing is a path. This is the two-face geometry
used for the wall rigidity assertion in XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Topology Surface GM14 GM11

/-- Two lines in empty faces, joined at their two ends, bound a dial
when a common boundary line joins the same ends. -/
theorem exists_isDial_of_two_faces {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {H : Drawing S} {C₁ C₂ P₁ P₂ K : Set S} {a b : S}
    (hC₁ : IsClosedDisc C₁) (hC₂ : IsClosedDisc C₂)
    (hP₁ : IsLineWithEnds P₁ a b) (hP₂ : IsLineWithEnds P₂ a b)
    (hK : IsLineWithEnds K a b) (hab : a ≠ b)
    (hPC₁ : P₁ ⊆ C₁) (hPC₂ : P₂ ⊆ C₂)
    (hKC₁ : K ⊆ discBd C₁) (hKC₂ : K ⊆ discBd C₂) (hKU : K ⊆ H.U)
    (hPU₁ : P₁ ∩ discBd C₁ ⊆ {a,b}) (hPU₂ : P₂ ∩ discBd C₂ ⊆ {a,b})
    (hEmpty₁ : C₁ ∩ H.U ⊆ discBd C₁) (hEmpty₂ : C₂ ∩ H.U ⊆ discBd C₂)
    (hMeet : C₁ ∩ C₂ ⊆ discBd C₁)
    (hNormal : (P₁ ∪ P₂) ∩ H.U ⊆ H.V)
    (hEnds : (P₁ ∪ P₂) ∩ H.V = {a,b}) :
    ∃ Δ, IsDial H (P₁ ∪ P₂) Δ := by
  obtain ⟨Δ₁,hΔC₁,hΔ₁,hbd₁,hSide₁,hU₁⟩ :=
    exists_face_subdisc hS hC₁ hP₁ hK hPC₁ hKC₁ hKU hPU₁ hEmpty₁
  obtain ⟨Δ₂,hΔC₂,hΔ₂,hbd₂,hSide₂,hU₂⟩ :=
    exists_face_subdisc hS hC₂ hP₂ hK hPC₂ hKC₂ hKU hPU₂ hEmpty₂
  have hKΔ₁ : K ⊆ Δ₁ := fun _ hx => (hSide₁.symm ▸ hx).1
  have hKΔ₂ : K ⊆ Δ₂ := fun _ hx => (hSide₂.symm ▸ hx).1
  have hInter : Δ₁ ∩ Δ₂ = K := by
    apply subset_antisymm
    · rintro x ⟨hx₁,hx₂⟩
      exact hSide₁ ▸ (show x ∈ Δ₁ ∩ discBd C₁ from
        ⟨hx₁,hMeet ⟨hΔC₁ hx₁,hΔC₂ hx₂⟩⟩)
    · intro x hx
      exact ⟨hKΔ₁ hx,hKΔ₂ hx⟩
  have hKb₁ : K ⊆ discBd Δ₁ := fun _ hx => hbd₁.symm ▸ Or.inr hx
  have hKb₂ : K ⊆ discBd Δ₂ := fun _ hx => hbd₂.symm ▸ Or.inr hx
  obtain ⟨hDisc,hBd⟩ := disc_union Δ₁ Δ₂ K a b hΔ₁ hΔ₂ hK hInter hKb₁ hKb₂
  have hBoundary : discBd (Δ₁ ∪ Δ₂) = P₁ ∪ P₂ := by
    rw [hBd,hbd₁,hbd₂]
    ext x
    constructor
    · rintro ⟨hx,hn⟩
      rcases hx with (hx | hx) | (hx | hx)
      · exact Or.inl hx
      · have hxEnds : x ∈ ({a,b} : Set S) := by
          by_contra h
          exact hn ⟨hx,h⟩
        rcases hxEnds with rfl | hxEnds
        · exact Or.inl hP₁.left_mem
        · rw [mem_singleton_iff] at hxEnds
          exact Or.inl (hxEnds.symm ▸ hP₁.right_mem)
      · exact Or.inr hx
      · have hxEnds : x ∈ ({a,b} : Set S) := by
          by_contra h
          exact hn ⟨hx,h⟩
        rcases hxEnds with rfl | hxEnds
        · exact Or.inl hP₁.left_mem
        · rw [mem_singleton_iff] at hxEnds
          exact Or.inl (hxEnds.symm ▸ hP₁.right_mem)
    · intro hx
      refine ⟨hx.elim (fun h => Or.inl (Or.inl h)) (fun h => Or.inr (Or.inl h)),?_⟩
      rintro ⟨hxK,hxEnds⟩
      exact hxEnds (hx.elim (fun h => hPU₁ ⟨h,hKC₁ hxK⟩)
        (fun h => hPU₂ ⟨h,hKC₂ hxK⟩))
  have hDrawing : H.U ∩ (Δ₁ ∪ Δ₂) = K := by
    rw [inter_comm,union_inter_distrib_right,hU₁,hU₂,union_self]
  refine ⟨Δ₁ ∪ Δ₂,isDial_of_line_intersection hDisc ?_ hNormal hab hEnds ?_⟩
  · rw [subBd_eq_frontier,GM11.IsClosedDisc.frontier_eq_discBd hS hDisc,hBoundary]
  · exact hDrawing.symm ▸ hK

end GraphMinor.GM16
