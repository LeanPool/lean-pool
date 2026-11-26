/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Rotation
import LeanPool.GraphMinor.GM07.Section46EdgeContacts
import LeanPool.GraphMinor.GM07.Section5b
import LeanPool.GraphMinor.Surface.ChartCells

/-!
# The three closed segments of a long edge

The split on page 225 of VII (4.6) uses two interior parameter values.
Each of the left, central and right closed segments is a line, even if
the old edge is a loop. Its open edge is the image of the open parameter
interval. These facts justify gluing the three line drawings.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface GraphMinor.GM11

universe u

/-- An interval that omits at least one end of an edge parameter is
injective, as required for the three pieces in VII (4.6), page 225. -/
theorem edge_parameter_injOn_Icc {S : Type u} [TopologicalSpace S]
    {J : Drawing S} {γ : Set S → unitInterval → S} (hγ : EdgePar J γ)
    {e : Set S} (he : e ∈ J.E) {a b : unitInterval} (hab : 0 < a ∨ b < 1) :
    InjOn (γ e) (Icc a b) := by
  intro x hx y hy hxy
  rcases edge_parameter_eq_or_ends hγ he hxy with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h
  · rcases hab with ha | hb
    · exact (not_le_of_gt ha hx.1).elim
    · exact (not_le_of_gt hb hy.2).elim
  · rcases hab with ha | hb
    · exact (not_le_of_gt ha hy.1).elim
    · exact (not_le_of_gt hb hx.2).elim

/-- The closed intervals used for linking and central pieces are lines,
in VII (4.6), page 225. -/
theorem edge_parameter_line_Icc {S : Type u} [TopologicalSpace S] [T2Space S]
    {J : Drawing S} {γ : Set S → unitInterval → S} (hγ : EdgePar J γ)
    {e : Set S} (he : e ∈ J.E) {a b : unitInterval} (hlt : a < b)
    (hab : 0 < a ∨ b < 1) :
    IsLineWithEnds (γ e '' Icc a b) (γ e a) (γ e b) :=
  isLineWithEnds_image_Icc_of_injOn (hγ.cont e he) hlt (edge_parameter_injOn_Icc hγ he hab)

/-- Removing the two ends of an injective closed parameter segment leaves
its open parameter image, the edge of the corresponding line drawing. -/
theorem image_Icc_diff_endpoints {S : Type u}
    {g : unitInterval → S} {a b : unitInterval} (hab : a < b)
    (hinj : InjOn g (Icc a b)) :
    (g '' Icc a b) \ {g a, g b} = g '' Ioo a b := by
  ext x
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hends⟩
    have hta : t ≠ a := fun h => hends (.inl (congrArg g h))
    have htb : t ≠ b := fun h => hends (.inr (congrArg g h))
    exact ⟨t, ⟨lt_of_le_of_ne ht.1 hta.symm, lt_of_le_of_ne ht.2 htb⟩, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩, ?_⟩
    rintro (h | h)
    · exact ht.1.ne' (hinj ⟨ht.1.le, ht.2.le⟩ ⟨le_rfl, hab.le⟩ h)
    · exact ht.2.ne (hinj ⟨ht.1.le, ht.2.le⟩ ⟨hab.le, le_rfl⟩ h)

/-- The full edge parameter covers precisely the closed edge. -/
theorem edge_parameter_range {S : Type u} [TopologicalSpace S] [T2Space S]
    {J : Drawing S} {γ : Set S → unitInterval → S} (hγ : EdgePar J γ)
    {e : Set S} (he : e ∈ J.E) : range (γ e) = closure e := by
  apply Subset.antisymm
  · rintro x ⟨t, rfl⟩
    have ht : t ∈ closure (Ioo (0 : unitInterval) 1) := by
      rw [closure_Ioo zero_ne_one]
      exact ⟨bot_le, le_top⟩
    have hx := image_closure_subset_closure_image (hγ.cont e he) ⟨t, ht, rfl⟩
    exact (congrArg (fun A => γ e t ∈ closure A) (hγ.image e he)).mp hx
  · apply closure_minimal _ (isCompact_range (hγ.cont e he)).isClosed
    intro x hx
    obtain ⟨t, _, rfl⟩ := (congrArg (fun A => x ∈ A) (hγ.image e he)).mpr hx
    exact mem_range_self t

/-- The old vertices on a closed edge are its two parameter ends. -/
theorem edge_parameter_old_vertices {S : Type u} [TopologicalSpace S] [T2Space S]
    {J : Drawing S} {γ : Set S → unitInterval → S} (hγ : EdgePar J γ)
    {e : Set S} (he : e ∈ J.E) :
    closure e ∩ J.V = {γ e 0, γ e 1} := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨t, rfl⟩ := (congrArg (fun A => x ∈ A) (edge_parameter_range hγ he)).mpr hx.1
    by_cases h0 : t = 0
    · exact .inl (congrArg (γ e) h0)
    by_cases h1 : t = 1
    · exact .inr (congrArg (γ e) h1)
    have ht : t ∈ Ioo (0 : unitInterval) 1 :=
      ⟨unitInterval.pos_iff_ne_zero.mpr h0, unitInterval.lt_one_iff_ne_one.mpr h1⟩
    have hxE : γ e t ∈ e :=
      (congrArg (fun A => γ e t ∈ A) (hγ.image e he)).mp ⟨t, ht, rfl⟩
    exact ((he.2.1 hxE).2 hx.2).elim
  · rintro x (rfl | rfl)
    · exact ⟨(congrArg (fun A => γ e 0 ∈ A) (edge_parameter_range hγ he)).mp (mem_range_self 0),
        hγ.zero e he⟩
    · exact ⟨(congrArg (fun A => γ e 1 ∈ A) (edge_parameter_range hγ he)).mp (mem_range_self 1),
        hγ.one e he⟩

/-- The closure of an open injective parameter segment is the closed
segment. These are the closures used for the contact counts on linking
and central edges in VII (4.6), page 225. -/
theorem closure_image_Ioo_eq_Icc {S : Type u} [TopologicalSpace S] [T2Space S]
    {J : Drawing S} {γ : Set S → unitInterval → S} (hγ : EdgePar J γ)
    {e : Set S} (he : e ∈ J.E) {a b : unitInterval} (hlt : a < b)
    (hab : 0 < a ∨ b < 1) :
    closure (γ e '' Ioo a b) = γ e '' Icc a b := by
  have hL := edge_parameter_line_Icc hγ he hlt hab
  have hinj := edge_parameter_injOn_Icc hγ he hab
  rw [← image_Icc_diff_endpoints hlt hinj]
  exact Subset.antisymm (closure_minimal sdiff_subset hL.isCompact.isClosed)
    hL.subset_closure_diff

end GraphMinor.GM07
