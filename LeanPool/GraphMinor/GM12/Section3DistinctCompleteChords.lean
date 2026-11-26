/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3CompleteChordCarrier

/-!
# Distinct complete chords meet only on the base

For the extraction used by XII (3.1), page 245, remove degenerate
chords and repeated endpoint pairs from the finite chord carrier.
Two remaining parameter gaps cannot overlap away from their contact
endpoints: such an overlap forces both pairs of endpoints to coincide.
Injectivity transfers this fact to the original path.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- The finite complete-chord reduction can be chosen with distinct
nondegenerate parameter intervals. Different chords meet only in the
solid base. -/
theorem exists_homotopic_path_in_distinct_complete_chords
    {S : Type*} [TopologicalSpace S] (hS : IsSurface S) {F : Set S}
    (hF : IsSolid F) {a b : S} (p : Path a b) (hpi : Function.Injective p)
    (ha : a ∈ F) (hb : b ∈ F) :
    ∃ (J : Finset (unitInterval × unitInterval)) (q : Path a b),
      p.Homotopic q ∧ range q ⊆ F ∪ ⋃ g ∈ J, p '' Icc g.1 g.2 ∧
      (∀ g ∈ J, g.1 < g.2 ∧ p g.1 ∈ F ∧ p g.2 ∈ F ∧
        Disjoint (p '' Ioo g.1 g.2) F) ∧
      ∀ g ∈ J, ∀ h ∈ J, g ≠ h → (p '' Icc g.1 g.2) ∩ (p '' Icc h.1 h.2) ⊆ F := by
  classical
  obtain ⟨n, l, r, q, hpq, hq, hdata⟩ :=
    exists_homotopic_path_in_finite_complete_chords hS hF p hpi ha hb
  let J := ((Finset.univ : Finset (Fin n)).filter (fun i => l i < r i)).image (fun i => (l i, r i))
  have hvalid : ∀ g ∈ J, g.1 < g.2 ∧ p g.1 ∈ F ∧ p g.2 ∈ F ∧
      Disjoint (p '' Ioo g.1 g.2) F := by
    intro g hg
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hg
    exact ⟨(Finset.mem_filter.mp hi).2, (hdata i).2⟩
  refine ⟨J, q, hpq, ?_, hvalid, ?_⟩
  · intro x hx
    rcases hq hx with hxF | hxJ
    · exact Or.inl hxF
    · obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp hxJ
      by_cases hlt : l i < r i
      · exact Or.inr (mem_iUnion₂.mpr ⟨(l i, r i), Finset.mem_image.mpr
          ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hlt⟩, rfl⟩, z, hz, rfl⟩)
      · have heq : l i = r i := le_antisymm (hdata i).1 (le_of_not_gt hlt)
        have hzl : z = l i := le_antisymm (hz.2.trans_eq heq.symm) hz.1
        exact Or.inl (hzl.symm ▸ (hdata i).2.1)
  · intro g hg h hh hne x hx
    obtain ⟨z, hz, rfl⟩ := hx.1
    obtain ⟨w, hw, he⟩ := hx.2
    have hwz : w = z := hpi he
    have hz' : z ∈ Icc h.1 h.2 := hwz ▸ hw
    have hgap : Disjoint (Ioo g.1 g.2) (p ⁻¹' F) := disjoint_left.mpr (by
      intro t ht htF
      exact disjoint_left.mp (hvalid g hg).2.2.2 ⟨t, ht, rfl⟩ htF)
    have hgap' : Disjoint (Ioo h.1 h.2) (p ⁻¹' F) := disjoint_left.mpr (by
      intro t ht htF
      exact disjoint_left.mp (hvalid h hh).2.2.2 ⟨t, ht, rfl⟩ htF)
    exact parameter_gaps_intersection_subset_contacts (hvalid g hg).2.1 (hvalid g hg).2.2.1
      (hvalid h hh).2.1 (hvalid h hh).2.2.1 hgap hgap' hne ⟨hz, hz'⟩

end GraphMinor.GM12
