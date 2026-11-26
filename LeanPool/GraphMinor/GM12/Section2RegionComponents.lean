/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2CurveCounts
import LeanPool.GraphMinor.GM11.Regions

/-!
# Arcs between different visits to one region contain vertices

Case 2 of XII (2.1), page 244, joins two different components of the
curve's intersection with a region. Each of the two arcs of the original
circle between the chord ends must contain a vertex. Otherwise that arc
would avoid the drawing, stay in the same region, and join the two
components inside their intersection. This supplies the strict length
reduction used by the induction.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- A preconnected part of a normal set joining different components
of its intersection with a region contains a vertex of the drawing.
This is the reason both original arcs in XII (2.1), Case 2 contain
vertices. -/
theorem vertices_nonempty_of_distinct_region_components {S : Type*} [TopologicalSpace S]
    {Γ : Drawing S} {r F A : Set S} (hr : r ∈ Γ.R) (hF : Γ.IsNormal F)
    (hA : IsPreconnected A) (hAF : A ⊆ F)
    {x y : S} (hxA : x ∈ A) (hyA : y ∈ A) (hxr : x ∈ r)
    (hdiff : connectedComponentIn (F ∩ r) x ≠ connectedComponentIn (F ∩ r) y) :
    (A ∩ Γ.V).Nonempty := by
  by_contra hnone
  have hoff : Disjoint A Γ.U := Set.disjoint_left.mpr fun z hz hzU =>
    hnone ⟨z, hz, hF ⟨hAF hz, hzU⟩⟩
  have hAr : A ⊆ r := subset_region hr hA hoff hxA hxr
  have hsub : A ⊆ F ∩ r := fun _ hz => ⟨hAF hz, hAr hz⟩
  have hyCC := hA.subset_connectedComponentIn hxA hsub hyA
  exact hdiff (connectedComponentIn_eq hyCC)

/-- The two original arcs between chord ends in different region
components both contain vertices. -/
theorem both_arcs_meet_vertices {S : Type*} [TopologicalSpace S]
    {Γ : Drawing S} {r F A B : Set S} {x y : S}
    (hr : r ∈ Γ.R) (hF : Γ.IsNormal F)
    (hA : IsLineWithEnds A x y) (hB : IsLineWithEnds B x y)
    (hAF : A ⊆ F) (hBF : B ⊆ F) (hxr : x ∈ r)
    (hdiff : connectedComponentIn (F ∩ r) x ≠ connectedComponentIn (F ∩ r) y) :
    (A ∩ Γ.V).Nonempty ∧ (B ∩ Γ.V).Nonempty := by
  have facts : ∀ {L : Set S}, IsLineWithEnds L x y →
      IsPreconnected L ∧ x ∈ L ∧ y ∈ L := by
    intro L hL
    obtain ⟨f, hf0, hf1⟩ := hL
    have hc : IsPreconnected L := by
      have heq : (fun t => (f t).val) '' univ = L := by
        ext z
        constructor
        · rintro ⟨t, _, rfl⟩; exact (f t).property
        · intro hz
          obtain ⟨t, ht⟩ := f.surjective ⟨z, hz⟩
          exact ⟨t, mem_univ _, congrArg Subtype.val ht⟩
      rw [← heq]
      exact isPreconnected_univ.image _ (continuous_subtype_val.comp f.continuous).continuousOn
    exact ⟨hc, hf0 ▸ (f 0).property, hf1 ▸ (f 1).property⟩
  obtain ⟨hAc, hxA, hyA⟩ := facts hA
  obtain ⟨hBc, hxB, hyB⟩ := facts hB
  exact ⟨vertices_nonempty_of_distinct_region_components hr hF hAc hAF hxA hyA hxr hdiff,
    vertices_nonempty_of_distinct_region_components hr hF hBc hBF hxB hyB hxr hdiff⟩

end GraphMinor.GM12
