/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM07.MinimalNet
import Mathlib.Data.Set.Card

/-!
# Fibers and contacts for exchanging a net side

In VII (2.6), page 218, pasting a paired boundary subarc and
cutting along a proper line replaces part of the seam. The
open interval of a paired side has exactly two preimages at
each image point. This applies at the ends of the subarc too
when they are inside the original side. These fiber equations
supply the contact counts without an extra endpoint allowance.
Normality of the new seam follows from normality of the old
seam and of the image of the cutting line.
-/

public section

namespace GraphMinor.GM07

open Set Surface

universe u

variable {S : Type u} [TopologicalSpace S]

/-- Every point in the open interval of a paired net side has
exactly its two paired points as preimages. This includes an
endpoint of a smaller subarc used in VII (2.6), page 218. -/
theorem Net.fiber_eq_pair_of_mem_Ioo (N : Net S) (i : Fin N.r)
    {t : unitInterval} (ht : t ∈ Ioo (0 : unitInterval) 1) :
    N.φ ⁻¹' {N.φ (N.f i t)} = {N.f i t, N.g i t} := by
  have hclosed : ∀ j s, N.f j s ∈ ({N.f i t, N.g i t} : Set N.D) ↔
      N.g j s ∈ ({N.f i t, N.g i t} : Set N.D) := by
    intro j s
    simp only [mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro (h | h)
      · obtain ⟨rfl, rfl⟩ := N.f_eq_iff ht h.symm
        exact .inr rfl
      · exact False.elim (N.internally_disjoint_gf i j t ht ⟨s, h⟩)
    · rintro (h | h)
      · exact False.elim (N.internally_disjoint_fg i j t ht ⟨s, h⟩)
      · obtain ⟨rfl, rfl⟩ := N.g_eq_iff ht h.symm
        exact .inl rfl
  ext x
  constructor
  · intro hx
    exact N.mem_of_eq hclosed (mem_singleton_iff.mp hx).symm (Or.inl rfl)
  · rintro (rfl | rfl)
    · exact mem_singleton _
    · exact (N.pasting_eq i t).symm

/-- The two preimages at an interior point of a paired side
remain distinct, including at subarc endpoints. -/
theorem Net.fiber_ncard_two_of_mem_Ioo (N : Net S) (i : Fin N.r)
    {t : unitInterval} (ht : t ∈ Ioo (0 : unitInterval) 1) :
    (N.φ ⁻¹' {N.φ (N.f i t)}).ncard = 2 := by
  rw [N.fiber_eq_pair_of_mem_Ioo i ht]
  exact ncard_pair (fun h => N.internally_disjoint_fg i i t ht ⟨t, h.symm⟩)

/-- The associated surjection is injective on one open paired
side, so its graph-contact count counts distinct image points. -/
theorem Net.injOn_image_open_side (N : Net S) (i : Fin N.r) :
    InjOn N.φ (N.f i '' Ioo (0 : unitInterval) 1) := by
  rintro x ⟨t, ht, rfl⟩ y ⟨s, hs, rfl⟩ heq
  have hy : N.f i s ∈ ({N.f i t, N.g i t} : Set N.D) := by
    rw [← N.fiber_eq_pair_of_mem_Ioo i ht]
    exact heq.symm
  rcases hy with h | h
  · exact h.symm
  · exact False.elim (N.internally_disjoint_gf i i t ht ⟨s, mem_singleton_iff.mp h⟩)

/-- At a point of the cutting line, the old fiber is a singleton
except at its two ends, where the other point is on the selected mate.
This describes all fibers used to compare the two replacement sides
in VII (2.6), page 218. -/
theorem Net.fiber_of_cutting_line_point (N : Net S) (i : Fin N.r)
    {u v : unitInterval} (hu : 0 < u) (huv : u < v) (hv : v < 1)
    {F : Set N.D} (hFbd : F ∩ bd N.D = {N.f i u, N.f i v})
    {x y : N.D} (hx : x ∈ F) (hxy : N.φ x = N.φ y) :
    y = x ∨ (x = N.f i u ∧ y = N.g i u) ∨ (x = N.f i v ∧ y = N.g i v) := by
  by_cases hxbd : x ∈ bd N.D
  · rcases hFbd.subset ⟨hx, hxbd⟩ with hxu | hxv
    · have hy : y ∈ ({N.f i u, N.g i u} : Set N.D) := by
        rw [← N.fiber_eq_pair_of_mem_Ioo i ⟨hu, huv.trans hv⟩]
        exact hxy.symm.trans (congrArg N.φ hxu)
      rcases hy with hy | hy
      · exact Or.inl (hy.trans hxu.symm)
      · exact Or.inr (Or.inl ⟨hxu, mem_singleton_iff.mp hy⟩)
    · have hxv' := mem_singleton_iff.mp hxv
      have hy : y ∈ ({N.f i v, N.g i v} : Set N.D) := by
        rw [← N.fiber_eq_pair_of_mem_Ioo i ⟨hu.trans huv, hv⟩]
        exact hxy.symm.trans (congrArg N.φ hxv')
      rcases hy with hy | hy
      · exact Or.inl (hy.trans hxv'.symm)
      · exact Or.inr (Or.inr ⟨hxv', mem_singleton_iff.mp hy⟩)
  · exact Or.inl (N.interior_inj x hxbd y hxy).symm

/-- The old associated map is injective on the whole cutting line
between two distinct interior points of a side, including its ends.
Thus its image is a line, not a loop, in this subarc exchange. -/
theorem Net.injOn_cutting_line (N : Net S) (i : Fin N.r)
    {u v : unitInterval} (hu : 0 < u) (huv : u < v) (hv : v < 1)
    {F : Set N.D} (hFbd : F ∩ bd N.D = {N.f i u, N.f i v}) : InjOn N.φ F := by
  have hFg : ∀ t ∈ Ioo (0 : unitInterval) 1, N.g i t ∉ F := by
    intro t ht htF
    have htbd := N.range_g_subset_bd i (mem_range_self t)
    rcases hFbd.subset ⟨htF, htbd⟩ with htu | htv
    · exact N.internally_disjoint_gf i i t ht ⟨u, htu.symm⟩
    · exact N.internally_disjoint_gf i i t ht ⟨v, (mem_singleton_iff.mp htv).symm⟩
  intro x hx y hy hxy
  rcases N.fiber_of_cutting_line_point i hu huv hv hFbd hx hxy with h | ⟨_, h⟩ | ⟨_, h⟩
  · exact h.symm
  · exact (hFg u ⟨hu, huv.trans hv⟩ (h ▸ hy)).elim
  · exact (hFg v ⟨hu.trans huv, hv⟩ (h ▸ hy)).elim

/-- Pullback normality of a cutting line gives normality of its
image in the original surface, as required in VII (2.6). -/
theorem Net.normal_image_of_pullback {N : Net S} {G : Drawing S}
    {G_D : Drawing N.D} (hPull : IsPullbackDrawing N.φ G G_D)
    {F : Set N.D} (hF : G_D.IsNormal F) : G.IsNormal (N.φ '' F) := by
  rintro x ⟨⟨y, hy, rfl⟩, hxU⟩
  have hyU : y ∈ G_D.U := hPull.1.symm ▸ hxU
  have hyV := hF ⟨hy, hyU⟩
  change y ∈ N.φ ⁻¹' G.V
  rw [← hPull.2]
  exact hyV

end GraphMinor.GM07
