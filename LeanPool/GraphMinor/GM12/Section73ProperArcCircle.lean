/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.GlueDiscs
import LeanPool.GraphMinor.GM11.PerimeterPull

/-!
# Compactifying a proper arc in a disc face

For the maximality verification in XII (7.3), page 261, an added
spoke lies in an old disc face except at its ends. Collapse the
complement of that face to infinity. The spoke becomes a circle in
the one-point compactification, which is a sphere. The Jordan curve
theorem can then separate the two sides of the added spoke.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 OnePoint

/-- The compactification collapse is injective on the open set it
retains. This is used for proper spokes in XII (7.3), page 261. -/
theorem collapse_injOn {S : Type*} (A : Set S) :
    InjOn (collapse A) A := by
  intro x hx y hy hxy
  rw [collapse_of_mem hx, collapse_of_mem hy] at hxy
  exact congrArg Subtype.val (OnePoint.coe_injective hxy)

/-- The finite points under compactification are exactly the points
of the retained set. -/
theorem collapse_ne_infty_iff {S : Type*} {A : Set S} {x : S} :
    collapse A x ≠ ∞ ↔ x ∈ A := by
  by_cases hx : x ∈ A
  · rw [collapse_of_mem hx]
    exact ⟨fun _ => hx, fun _ => OnePoint.coe_ne_infty _⟩
  · rw [collapse_of_notMem hx]
    exact ⟨fun h => False.elim (h rfl), fun h => False.elim (hx h)⟩

/-- A proper arc across an open disc becomes a circle when its
outside is collapsed to infinity. This is the separation step for
an added radial spoke in XII (7.3), page 261. -/
theorem isOArc_collapse_proper_line
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {A L : Set S} {a b : S} (hA : IsOpenDisc A) (hL : IsLineWithEnds L a b)
    (ha : a ∉ A) (hb : b ∉ A) (hinside : L \ {a, b} ⊆ A) :
    IsOArc (collapse A '' L) := by
  obtain ⟨hSphere, _⟩ := IsSphere.isClosedSurface (isSphere_onePoint hA)
  let : T2Space (OnePoint A) := hSphere.2.1
  obtain ⟨p, hp0, hp1⟩ := hL
  let m : unitInterval → OnePoint A := fun t => collapse A (p t).val
  have hmc : Continuous m := (continuous_collapse hA.1).comp
    (continuous_subtype_val.comp p.continuous)
  have hm0 : m 0 = ∞ := by
    change collapse A (p 0).val = ∞
    rw [hp0, collapse_of_notMem ha]
  have hm1 : m 1 = ∞ := by
    change collapse A (p 1).val = ∞
    rw [hp1, collapse_of_notMem hb]
  have hinterior : ∀ t ∈ Ioo (0 : unitInterval) 1, (p t).val ∈ A := by
    intro t ht
    apply hinside
    refine ⟨(p t).property, ?_⟩
    rintro (hpa | hpb)
    · have ht0 : t = 0 := p.injective (Subtype.ext (hpa.trans hp0.symm))
      exact ht.1.ne' ht0
    · have ht1 : t = 1 := p.injective (Subtype.ext (hpb.trans hp1.symm))
      exact ht.2.ne ht1
  have hmi : InjOn m (Ioo (0 : unitInterval) 1) := by
    intro s hs t ht hst
    exact p.injective (Subtype.ext (collapse_injOn A (hinterior s hs) (hinterior t ht) hst))
  have hmne : ∀ t ∈ Ioo (0 : unitInterval) 1, m t ≠ m 0 := by
    intro t ht
    rw [hm0]
    exact collapse_ne_infty_iff.mpr (hinterior t ht)
  have hrange : range m = collapse A '' L := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨(p t).val, (p t).property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨p.symm ⟨x, hx⟩, congrArg (collapse A) (congrArg Subtype.val (p.apply_symm_apply ⟨x,
        hx⟩))⟩
  exact hrange ▸ isOArc_of_loop hmc (hm0.trans hm1.symm) hmi hmne

end GraphMinor.GM12
