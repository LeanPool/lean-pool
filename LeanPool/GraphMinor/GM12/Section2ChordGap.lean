/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.RadialCorners

/-!
# The minimal chord in the second case of XII (2.1)

On page 244, the proof joins two components of the curve in one region
and takes a minimal line between them. Along an arc joining two disjoint
closed sets, first take the first point of the second set, then the last
point of the first set before it. The open segment between these points
misses both sets. Applied to one component and the union of the others,
this gives the required minimal line.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- Along a continuous curve from one disjoint closed set to another,
there is an interval with its ends in the two sets and its interior
outside both. Only closedness of their parameter preimages is needed. -/
theorem exists_parameter_gap {S : Type*} {g : unitInterval → S} {A B : Set S}
    (hA : IsClosed (g ⁻¹' A)) (hB : IsClosed (g ⁻¹' B))
    (hdis : Disjoint A B) (h0 : g 0 ∈ A) (h1 : g 1 ∈ B) :
    ∃ a b : unitInterval, a < b ∧ g a ∈ A ∧ g b ∈ B ∧
      ∀ t ∈ Ioo a b, g t ∉ A ∪ B := by
  obtain ⟨b, hb, hbmin⟩ := hB.isCompact.exists_isLeast ⟨1, h1⟩
  have h0b : (0 : unitInterval) ≤ b := b.property.1
  have hAc : IsCompact ((g ⁻¹' A) ∩ Iic b) := (hA.inter isClosed_Iic).isCompact
  obtain ⟨a, ⟨ha, hab⟩, hamax⟩ := hAc.exists_isGreatest ⟨0, h0, h0b⟩
  have hab' : a < b := lt_of_le_of_ne hab (by
    intro heq
    exact Set.disjoint_left.mp hdis ha (heq.symm ▸ hb))
  refine ⟨a, b, hab', ha, hb, ?_⟩
  intro t ht hmem
  rcases hmem with htA | htB
  · exact ht.1.not_ge (hamax ⟨htA, ht.2.le⟩)
  · exact ht.2.not_ge (hbmin htB)

/-- The minimal-line construction in Case 2 of XII (2.1), page 244.
An arc in the region joining two disjoint closed pieces of the curve
contains a subline whose interior misses the curve. -/
theorem exists_minimal_region_chord {S : Type*} [TopologicalSpace S] [T2Space S]
    {r F A B : Set S} {g : unitInterval → S} (hg : Continuous g)
    (hinj : Function.Injective g) (hgr : range g ⊆ r)
    (hcover : F ∩ r ⊆ A ∪ B)
    (hA : IsClosed (g ⁻¹' A)) (hB : IsClosed (g ⁻¹' B))
    (hdis : Disjoint A B) (h0 : g 0 ∈ A) (h1 : g 1 ∈ B) :
    ∃ (L : Set S) (a b : S), IsLineWithEnds L a b ∧ L ⊆ r ∧
      a ∈ A ∧ b ∈ B ∧ a ≠ b ∧ Disjoint (L \ {a, b}) F := by
  obtain ⟨s, t, hst, hsA, htB, hgap⟩ := exists_parameter_gap hA hB hdis h0 h1
  refine ⟨g '' Icc s t, g s, g t, isLine_piece hg hinj hst,
    (image_subset_range _ _).trans hgr, hsA, htB, ?_, Set.disjoint_left.mpr ?_⟩
  · exact fun h => hst.ne (hinj h)
  · rintro x ⟨⟨u, hu, rfl⟩, hends⟩ huF
    have hus : s < u := lt_of_le_of_ne hu.1 (by
      intro heq
      exact hends (Or.inl (congrArg g heq.symm)))
    have hut : u < t := lt_of_le_of_ne hu.2 (by
      intro heq
      exact hends (Or.inr (congrArg g heq)))
    exact hgap u ⟨hus, hut⟩ (hcover ⟨huF, hgr (mem_range_self u)⟩)

end GraphMinor.GM12
