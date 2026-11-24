/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
public import LeanPool.GraphMinor.Surface.CrossCut
import LeanPool.GraphMinor.Surface.DiscUnion
import LeanPool.GraphMinor.Surface.DiscGrow
import LeanPool.GraphMinor.Surface.Wedge
import LeanPool.GraphMinor.Surface.Disc

/-!
# The boundary after pasting the net pieces

VII (2.6), page 218, pastes the selected boundary subarc to
its mate. The interior of the pasted arc leaves the boundary
of the new disc, and its two ends remain. Apply the union-of-
discs boundary formula to the two images in the disc model.
This makes the endpoint terms explicit for the net count.
-/

public section

namespace GraphMinor.GM07

open Set Topology Metric Surface

/-- The boundary of a two-piece pasting model consists of the
two old boundaries minus the open pasted arc. This is the
boundary calculation for VII (2.6), page 218. -/
theorem boundary_of_disc_pasting_model
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : IsClosedDisc A) (hB : IsClosedDisc B)
    (f : unitInterval → X) (g : unitInterval → Y) (hf : IsArcMap f) (_hg : IsArcMap g)
    (hfbd : range f ⊆ discBd A) (hgbd : range g ⊆ discBd B)
    (p : X → ℂ) (q : Y → ℂ) (hpc : ContinuousOn p A) (hqc : ContinuousOn q B)
    (hpi : InjOn p A) (hqi : InjOn q B)
    (hcover : p '' A ∪ q '' B = closedBall (0 : ℂ) 1)
    (hmatch : ∀ x ∈ A, ∀ y ∈ B, p x = q y ↔ ∃ t, x = f t ∧ y = g t)
    (hpair : ∀ t, p (f t) = q (g t)) :
    sphere (0 : ℂ) 1 = (p '' discBd A ∪ q '' discBd B) \
      (p '' range f \ {p (f 0), p (f 1)}) := by
  let : Nonempty X := ⟨hA.isPathConnected.nonempty.some⟩
  let : Nonempty Y := ⟨hB.isPathConnected.nonempty.some⟩
  obtain ⟨hPA, hbPA⟩ := isClosedDisc_image_injOn hA hA.isCompact hpc hpi
  obtain ⟨hQB, hbQB⟩ := isClosedDisc_image_injOn hB hB.isCompact hqc hqi
  have hfA : ∀ t, f t ∈ A := fun t => discBd_subset A (hfbd ⟨t, rfl⟩)
  have hgB : ∀ t, g t ∈ B := fun t => discBd_subset B (hgbd ⟨t, rfl⟩)
  have hI : p '' A ∩ q '' B = p '' range f := by
    apply Subset.antisymm
    · rintro z ⟨⟨x, hx, rfl⟩, ⟨y, hy, hyx⟩⟩
      obtain ⟨t, rfl, hyt⟩ := (hmatch x hx y hy).mp hyx.symm
      exact mem_image_of_mem p (mem_range_self t)
    · rintro z ⟨x, ⟨t, rfl⟩, rfl⟩
      exact ⟨mem_image_of_mem p (hfA t), ⟨g t, hgB t, (hpair t).symm⟩⟩
  have hpf : IsArcMap (p ∘ f) :=
    ⟨hpc.comp_continuous hf.1 hfA, fun s t heq => hf.2 (hpi (hfA s) (hfA t) heq)⟩
  have hline : IsLineWithEnds (p '' range f) (p (f 0)) (p (f 1)) := by
    simpa only [range_comp, Function.comp_apply] using hpf.isLineWithEnds
  have hbdA : p '' range f ⊆ discBd (p '' A) := by
    rw [hbPA]
    exact image_mono hfbd
  have hbdB : p '' range f ⊆ discBd (q '' B) := by
    rw [hbQB]
    rintro z ⟨x, ⟨t, rfl⟩, rfl⟩
    exact ⟨g t, hgbd ⟨t, rfl⟩, (hpair t).symm⟩
  have hh := (disc_union (p '' A) (q '' B) (p '' range f) (p (f 0)) (p (f 1))
    hPA hQB hline hI hbdA hbdB).2
  rw [hcover, isClosedDisc_closedBall.2, hbPA, hbQB] at hh
  exact hh

/-- A point of the first piece remains on the pasted boundary
exactly when it was on that piece's boundary and outside the
open pasted arc. In particular the two arc ends remain. -/
theorem mem_boundary_of_disc_pasting_model
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : IsClosedDisc A) (hB : IsClosedDisc B)
    (f : unitInterval → X) (g : unitInterval → Y) (hf : IsArcMap f) (hg : IsArcMap g)
    (hfbd : range f ⊆ discBd A) (hgbd : range g ⊆ discBd B)
    (p : X → ℂ) (q : Y → ℂ) (hpc : ContinuousOn p A) (hqc : ContinuousOn q B)
    (hpi : InjOn p A) (hqi : InjOn q B)
    (hcover : p '' A ∪ q '' B = closedBall (0 : ℂ) 1)
    (hmatch : ∀ x ∈ A, ∀ y ∈ B, p x = q y ↔ ∃ t, x = f t ∧ y = g t)
    (hpair : ∀ t, p (f t) = q (g t)) {x : X} (hx : x ∈ A) :
    p x ∈ sphere (0 : ℂ) 1 ↔ x ∈ discBd A ∧ x ∉ f '' Ioo (0 : unitInterval) 1 := by
  have hfA : ∀ t, f t ∈ A := fun t => discBd_subset A (hfbd ⟨t, rfl⟩)
  have hU : p x ∈ p '' discBd A ∪ q '' discBd B ↔ x ∈ discBd A := by
    constructor
    · rintro (⟨z, hz, hzx⟩ | ⟨y, hy, hyx⟩)
      · exact hpi (discBd_subset A hz) hx hzx ▸ hz
      · obtain ⟨t, rfl, hyt⟩ := (hmatch x hx y (discBd_subset B hy)).mp hyx.symm
        exact hfbd ⟨t, rfl⟩
    · exact fun h => Or.inl (mem_image_of_mem p h)
  have hK : p x ∈ p '' range f \ {p (f 0), p (f 1)} ↔
      x ∈ f '' Ioo (0 : unitInterval) 1 := by
    constructor
    · rintro ⟨⟨z, ⟨t, rfl⟩, htx⟩, hnot⟩
      have hfx : f t = x := hpi (hfA t) hx htx
      have ht0 : t ≠ 0 := by
        intro ht
        exact hnot (Or.inl (htx.symm.trans (by rw [ht])))
      have ht1 : t ≠ 1 := by
        intro ht
        exact hnot (Or.inr (htx.symm.trans (by rw [ht])))
      exact ⟨t, ⟨unitInterval.pos_iff_ne_zero.mpr ht0,
        unitInterval.lt_one_iff_ne_one.mpr ht1⟩, hfx⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨mem_image_of_mem p (mem_range_self t), ?_⟩
      rintro (h0 | h1)
      · have heq := hf.2 (hpi (hfA t) (hfA 0) h0)
        exact ht.1.ne' heq
      · have heq := hf.2 (hpi (hfA t) (hfA 1) (mem_singleton_iff.mp h1))
        exact ht.2.ne heq
  rw [boundary_of_disc_pasting_model hA hB f g hf hg hfbd hgbd p q hpc hqc hpi hqi
    hcover hmatch hpair]
  exact and_congr hU (not_congr hK)

end GraphMinor.GM07
