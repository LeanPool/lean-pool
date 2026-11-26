/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
public import LeanPool.GraphMinor.Surface.ArcTools
import LeanPool.GraphMinor.GM07.NetSwapArcs
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# The old sides on the retained piece of the cut disc

In VII (2.6), page 218, only the selected subarc is pasted to
its mate. Every other paired side stays on the retained disc,
as do the two outer portions of the selected side. Internal
disjointness of the old sides and the two cut endpoints prove
these boundary containments.
-/

public section

namespace GraphMinor.GM07

open Set Surface

/-- Locate all unchanged side maps and the two surviving parts
of the selected side on the boundary of the retained cut piece
in the net exchange of VII (2.6), page 218. -/
theorem Net.sides_on_retained_piece
    {S : Type*} [TopologicalSpace S] (N : Net S) (i : Fin N.r)
    (u v : unitInterval) (hu : 0 < u) (huv : u < v) (hv : v < 1)
    {F C B : Set N.D} (hF : IsLineWithEnds F (N.f i u) (N.f i v))
    (hcover : range (pieceA (N.f i) u.val v.val) ∪ C = bd N.D)
    (hB : discBd B = C ∪ F) :
    (∀ j, j ≠ i → range (N.f j) ⊆ discBd B) ∧
      (∀ j, range (N.g j) ⊆ discBd B) ∧
      N.f i '' Icc 0 u ⊆ discBd B ∧ N.f i '' Icc v 1 ⊆ discBd B := by
  have hcut : range (pieceA (N.f i) u.val v.val) = N.f i '' Icc u v :=
    range_pieceA_unitInterval (N.f i) u v huv.le
  have hout : ∀ x ∈ bd N.D, x ∉ range (pieceA (N.f i) u.val v.val) → x ∈ discBd B := by
    intro x hxbd hxcut
    have hxC : x ∈ C := (hcover.symm ▸ hxbd).resolve_left hxcut
    exact hB ▸ Or.inl hxC
  have hinner : ∀ w ∈ Icc u v, w ∈ Ioo (0 : unitInterval) 1 :=
    fun w hw => ⟨hu.trans_le hw.1, hw.2.trans_lt hv⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hji x hxj
    apply hout x (N.range_f_subset_bd j hxj)
    rw [hcut]
    rintro ⟨w, hw, hwx⟩
    exact N.internally_disjoint_ff i j hji.symm w (hinner w hw) (hwx.symm ▸ hxj)
  · intro j x hxj
    apply hout x (N.range_g_subset_bd j hxj)
    rw [hcut]
    rintro ⟨w, hw, hwx⟩
    exact N.internally_disjoint_fg i j w (hinner w hw) (hwx.symm ▸ hxj)
  · rintro x ⟨t, ht, rfl⟩
    rcases eq_or_lt_of_le ht.2 with htu | htu
    · exact hB ▸ Or.inr (htu.symm ▸ hF.left_mem)
    · apply hout _ (N.range_f_subset_bd i (mem_range_self t))
      rw [hcut]
      rintro ⟨w, hw, hwt⟩
      have hwt' : w = t := N.injective_f i hwt
      exact (not_le_of_gt htu) (hwt' ▸ hw.1)
  · rintro x ⟨t, ht, rfl⟩
    rcases eq_or_lt_of_le ht.1 with hvt | hvt
    · exact hB ▸ Or.inr (hvt ▸ hF.right_mem)
    · apply hout _ (N.range_f_subset_bd i (mem_range_self t))
      rw [hcut]
      rintro ⟨w, hw, hwt⟩
      have hwt' : w = t := N.injective_f i hwt
      exact (not_le_of_gt hvt) (hwt' ▸ hw.2)

/-- The cutting line misses every unchanged side. Its only old boundary
contacts are strictly inside the selected side, so they cannot lie on
any other side. This is the disjointness needed for the net exchange
in VII (2.6), page 218. -/
theorem Net.cutting_line_disjoint_other_sides
    {S : Type*} [TopologicalSpace S] (N : Net S) (i : Fin N.r)
    {u v : unitInterval} (hu : 0 < u) (huv : u < v) (hv : v < 1)
    {F : Set N.D} (hFbd : F ∩ bd N.D = {N.f i u, N.f i v}) :
    (∀ j, j ≠ i → Disjoint F (range (N.f j))) ∧
      (∀ j, Disjoint F (range (N.g j))) := by
  have hu' : u ∈ Ioo (0 : unitInterval) 1 := ⟨hu, huv.trans hv⟩
  have hv' : v ∈ Ioo (0 : unitInterval) 1 := ⟨hu.trans huv, hv⟩
  constructor
  · intro j hji
    apply disjoint_left.mpr
    intro x hxF hxj
    rcases hFbd.subset ⟨hxF, N.range_f_subset_bd j hxj⟩ with hxu | hxv
    · exact N.internally_disjoint_ff i j hji.symm u hu' (hxu ▸ hxj)
    · exact N.internally_disjoint_ff i j hji.symm v hv'
        ((mem_singleton_iff.mp hxv) ▸ hxj)
  · intro j
    apply disjoint_left.mpr
    intro x hxF hxj
    rcases hFbd.subset ⟨hxF, N.range_g_subset_bd j hxj⟩ with hxu | hxv
    · exact N.internally_disjoint_fg i j u hu' (hxu ▸ hxj)
    · exact N.internally_disjoint_fg i j v hv'
        ((mem_singleton_iff.mp hxv) ▸ hxj)

/-- In the pasted disc, the attached piece cannot meet any retained
side except the selected mate. The cross-piece fiber equation puts
any such meeting strictly inside that mate, which the old net's
internal disjointness excludes. This is part of the new-net
construction in VII (2.6), page 218. -/
theorem Net.attached_piece_disjoint_other_sides
    {S T : Type*} [TopologicalSpace S] (N : Net S) (i : Fin N.r)
    {u v : unitInterval} (hu : 0 < u) (huv : u < v) (hv : v < 1)
    {A B : Set N.D} (α : A → T) (β : B → T)
    (hcross : ∀ (x : A) (y : B), α x = β y ↔
      ∃ t, x.val = pieceA (N.f i) u.val v.val t ∧
        y.val = pieceA (N.g i) u.val v.val t) :
    (∀ j, Disjoint (range α) (β '' {y : B | y.val ∈ range (N.f j)})) ∧
      (∀ j, j ≠ i →
        Disjoint (range α) (β '' {y : B | y.val ∈ range (N.g j)})) := by
  have hinner : ∀ w ∈ Icc u v, w ∈ Ioo (0 : unitInterval) 1 :=
    fun w hw => ⟨hu.trans_le hw.1, hw.2.trans_lt hv⟩
  have hseg := range_pieceA_unitInterval (N.g i) u v huv.le
  constructor
  · intro j
    apply disjoint_left.mpr
    rintro z ⟨x, rfl⟩ ⟨y, hy, heq⟩
    obtain ⟨t, _, hyt⟩ := (hcross x y).mp heq.symm
    obtain ⟨w, hw, hwy⟩ := hseg.subset ⟨t, hyt.symm⟩
    exact N.internally_disjoint_gf i j w (hinner w hw) (hwy.symm ▸ hy)
  · intro j hji
    apply disjoint_left.mpr
    rintro z ⟨x, rfl⟩ ⟨y, hy, heq⟩
    obtain ⟨t, _, hyt⟩ := (hcross x y).mp heq.symm
    obtain ⟨w, hw, hwy⟩ := hseg.subset ⟨t, hyt.symm⟩
    exact N.internally_disjoint_gg i j hji.symm w (hinner w hw) (hwy.symm ▸ hy)

end GraphMinor.GM07
