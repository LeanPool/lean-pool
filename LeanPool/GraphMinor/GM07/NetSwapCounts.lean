/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
public import LeanPool.GraphMinor.Surface.ArcTools
import LeanPool.GraphMinor.GM07.MinimalNet
import Mathlib.Data.Set.Card

/-!
# Contact counts in the interior of a net disc

The count in VII (2.6), page 218, uses distinct image points
of the proper cutting line with its ends removed. A net makes
no identifications at these points. Its finite fibers also
make the full preimage of a finite graph vertex set finite.
Thus the boundary and interior contact counts use finite sets.
-/

public section

namespace GraphMinor.GM07

open Set Surface

/-- A finite vertex set has finite preimage under the associated
surjection of a net. This justifies the counts in VII (2.6). -/
theorem Net.finite_preimage_of_finite
    {S : Type*} [TopologicalSpace S] (N : Net S) {V : Set S} (hV : V.Finite) :
    (N.φ ⁻¹' V).Finite := by
  have heq : N.φ ⁻¹' V = ⋃ v ∈ V, N.φ ⁻¹' {v} := by
    ext x
    simp only [mem_preimage, mem_iUnion, mem_singleton_iff]
    exact ⟨fun h => ⟨N.φ x, h, rfl⟩, fun ⟨v, hv, hxv⟩ => hxv.symm ▸ hv⟩
  rw [heq]
  exact hV.biUnion (fun v hv => N.finite_fiber v)

/-- The interior of a proper cutting line has singleton fibers
in the old disc of the net. This is the unpasted term of the
exchange count in VII (2.6), page 218. -/
theorem Net.preimage_image_line_interior
    {S : Type*} [TopologicalSpace S] (N : Net S)
    {F : Set N.D} {s t : N.D} (hbd : F ∩ bd N.D = {s, t}) :
    N.φ ⁻¹' (N.φ '' (F \ {s, t})) = F \ {s, t} := by
  apply Subset.antisymm
  · rintro x ⟨y, hy, hyx⟩
    have hybd : y ∉ bd N.D := fun h => hy.2 (hbd.subset ⟨hy.1, h⟩)
    exact (N.interior_inj y hybd x hyx) ▸ hy
  · exact subset_preimage_image _ _

/-- Distinct points of the cutting line away from its ends have
distinct images under the old associated surjection. -/
theorem Net.injOn_line_interior
    {S : Type*} [TopologicalSpace S] (N : Net S)
    {F : Set N.D} {s t : N.D} (hbd : F ∩ bd N.D = {s, t}) :
    InjOn N.φ (F \ {s, t}) := by
  intro x hx y hy heq
  have hxbd : x ∉ bd N.D := fun h => hx.2 (hbd.subset ⟨hx.1, h⟩)
  exact N.interior_inj x hxbd y heq

/-- The old disc's interior contact count equals the image count
printed in VII (2.6), page 218. -/
theorem Net.ncard_line_interior_contacts
    {S : Type*} [TopologicalSpace S] (N : Net S)
    {F : Set N.D} {s t : N.D} (hbd : F ∩ bd N.D = {s, t}) (V : Set S) :
    ((F \ {s, t}) ∩ N.φ ⁻¹' V).ncard = (N.φ '' (F \ {s, t}) ∩ V).ncard := by
  have hi := (N.injOn_line_interior hbd).mono (inter_subset_left :
    (F \ {s, t}) ∩ N.φ ⁻¹' V ⊆ F \ {s, t})
  rw [← hi.ncard_image, image_inter_preimage]

/-- When two boundary contact sets are pasted, their common
open arc disappears and their common ends stay once. The
formula isolates the endpoint contribution, which cancels
between cutting and pasting in VII (2.6), page 218. -/
theorem ncard_boundary_after_pasting
    {X : Type*} (P Q E : Set X) (hP : P.Finite) (hQ : Q.Finite) :
    ((P ∪ Q) \ ((P ∩ Q) \ E)).ncard +
        2 * ((P ∩ Q) \ E).ncard + ((P ∩ Q) ∩ E).ncard = P.ncard + Q.ncard := by
  have hK : (P ∩ Q) \ E ⊆ P ∪ Q := fun x hx => Or.inl hx.1.1
  have hu := ncard_sdiff_add_ncard_of_subset hK (hP.union hQ)
  have hi : ((P ∩ Q) \ ((P ∩ Q) ∩ E)).ncard + ((P ∩ Q) ∩ E).ncard = (P ∩ Q).ncard :=
    ncard_sdiff_add_ncard_of_subset inter_subset_left (hP.subset inter_subset_left)
  have heq : (P ∩ Q) \ ((P ∩ Q) ∩ E) = (P ∩ Q) \ E := by
    ext x
    constructor
    · rintro ⟨hx, hn⟩
      exact ⟨hx, fun he => hn ⟨hx, he⟩⟩
    · rintro ⟨hx, hn⟩
      exact ⟨hx, fun he => hn he.2⟩
  rw [heq] at hi
  have hsum := ncard_union_add_ncard_inter P Q hP hQ
  omega

/-- Splitting a boundary along a line counts an inner contact twice
and an endpoint contact once in addition to the old boundary count.
This finite-set identity keeps the endpoint contribution exact. -/
theorem ncard_cut_contacts
    {X : Type*} (K A B F E W : Set X) (hW : W.Finite)
    (hUnion : A ∪ B = K ∪ F) (hInter : A ∩ B = F) (hEnds : K ∩ F = E) :
    (A ∩ W).ncard + (B ∩ W).ncard =
      (K ∩ W).ncard + 2 * ((F \ E) ∩ W).ncard + (E ∩ W).ncard := by
  have hP : (A ∩ W).Finite := hW.subset inter_subset_right
  have hQ : (B ∩ W).Finite := hW.subset inter_subset_right
  have hI : (A ∩ W) ∩ (B ∩ W) = F ∩ W := by
    rw [← hInter]
    ext x
    simp only [mem_inter_iff]
    tauto
  have hU : (A ∩ W) ∪ (B ∩ W) = (K ∪ F) ∩ W := by
    rw [← hUnion]
    ext x
    simp only [mem_inter_iff, mem_union]
    tauto
  have hEsub : E ⊆ F := hEnds ▸ inter_subset_right
  have hRem : ((A ∩ W) ∪ (B ∩ W)) \ (((A ∩ W) ∩ (B ∩ W)) \ E) = K ∩ W := by
    rw [hI, hU]
    ext x
    have he : x ∈ E ↔ x ∈ K ∧ x ∈ F := by rw [← hEnds]; rfl
    simp only [mem_sdiff, mem_inter_iff, mem_union]
    tauto
  have hInner : ((A ∩ W) ∩ (B ∩ W)) \ E = (F \ E) ∩ W := by
    rw [hI]
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  have hEnd : ((A ∩ W) ∩ (B ∩ W)) ∩ E = E ∩ W := by
    rw [hI]
    ext x
    constructor
    · exact fun h => ⟨h.2, h.1.2⟩
    · exact fun h => ⟨⟨hEsub h.1, h.2⟩, h.1⟩
  have h := ncard_boundary_after_pasting (A ∩ W) (B ∩ W) E hP hQ
  rw [hRem, hInner, hEnd] at h
  exact h.symm

/-- The two cut pieces contain exactly the old boundary contacts,
two copies of each inner cutting-line contact, and one extra copy
of each cutting endpoint. The latter term cancels on pasting, even
when a cutting endpoint is a graph vertex. This is the cutting half
of the count in VII (2.6), page 218. -/
theorem Net.ncard_cut_piece_contacts
    {S : Type*} [TopologicalSpace S] (N : Net S) (i : Fin N.r)
    (u v : unitInterval) {F C A B : Set N.D}
    (hI : A ∩ B = F)
    (hAd : discBd A = range (pieceA (N.f i) u.val v.val) ∪ F)
    (hBd : discBd B = C ∪ F)
    (hcover : range (pieceA (N.f i) u.val v.val) ∪ C = bd N.D)
    (hFbd : F ∩ bd N.D = {N.f i u, N.f i v})
    (V : Set S) (hV : V.Finite) :
    (discBd A ∩ N.φ ⁻¹' V).ncard + (discBd B ∩ N.φ ⁻¹' V).ncard =
      (bd N.D ∩ N.φ ⁻¹' V).ncard +
        2 * (N.φ '' (F \ {N.f i u, N.f i v}) ∩ V).ncard +
        ({N.f i u, N.f i v} ∩ N.φ ⁻¹' V).ncard := by
  have hUnion : discBd A ∪ discBd B = bd N.D ∪ F := by
    rw [hAd, hBd, ← hcover]
    ext x
    simp only [mem_union]
    tauto
  have hInter : discBd A ∩ discBd B = F := by
    apply Subset.antisymm
    · exact fun x hx => hI ▸ ⟨discBd_subset A hx.1, discBd_subset B hx.2⟩
    · intro x hx
      exact ⟨hAd ▸ Or.inr hx, hBd ▸ Or.inr hx⟩
  have hEnds : bd N.D ∩ F = {N.f i u, N.f i v} := by rw [inter_comm, hFbd]
  have h := ncard_cut_contacts (bd N.D) (discBd A) (discBd B) F
    {N.f i u, N.f i v} (N.φ ⁻¹' V) (N.finite_preimage_of_finite hV) hUnion hInter hEnds
  rw [N.ncard_line_interior_contacts hFbd V] at h
  exact h

end GraphMinor.GM07
