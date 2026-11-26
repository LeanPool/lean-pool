/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73CircleArcFibres
import Mathlib.Topology.Separation.Hausdorff

/-!
# Circle parameters for the two kinds of circuit fibre

In XII (7.3), Claim (1), page 262, the old circuit meets the
collapsed star in either one point or one arc. In the point case
the collapse remains injective on the circle. The arc case uses
the complementary-arc parameterization and the homotopy removing
the constant arc. Both give embedded old and new parameters and
a homotopy from the collapsed old parameter to the new one.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- Choose embedded boundary parameters before and after a
collapse whose intersection with the old circle is a point or
an arc. This treats both circuit alternatives in XII (7.3),
Claim (1), page 262. -/
theorem exists_circle_parameters_of_fibre_shape
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {F A Z : Set S} (hF : IsOArc F)
    (hshape : (F ∩ A).Subsingleton ∨ ∃ p q, IsLineWithEnds (F ∩ A) p q)
    (f : C(S, S))
    (hfibre : ∀ x y, f x = f y ↔ x = y ∨ (x ∈ A ∧ y ∈ A))
    (hZ : f '' F ⊆ Z) :
    ∃ φ ψ : C(Circle, S), IsEmbedding φ ∧ IsEmbedding ψ ∧
      range φ = F ∧ range ψ = f '' F ∧
      ClosedCurvesHomotopicIn Z (f.comp φ) ψ := by
  rcases hshape with hsingle | ⟨p, q, hline⟩
  · obtain ⟨e⟩ := hF
    let φ : C(Circle, S) := ⟨fun z => (e z).val, continuous_subtype_val.comp e.continuous⟩
    have hφ : IsEmbedding φ := IsEmbedding.subtypeVal.comp e.isEmbedding
    have hrange : range φ = F := by
      ext x
      constructor
      · rintro ⟨z, rfl⟩
        exact (e z).property
      · intro hx
        exact ⟨e.symm ⟨x, hx⟩, congrArg Subtype.val (e.apply_symm_apply _)⟩
    let ψ : C(Circle, S) := f.comp φ
    have hinj : Function.Injective ψ := by
      intro z w heq
      rcases (hfibre (φ z) (φ w)).mp heq with heq | hA
      · exact hφ.injective heq
      · exact hφ.injective (hsingle ⟨(e z).property, hA.1⟩ ⟨(e w).property, hA.2⟩)
    have hψrange : range ψ = f '' F := by
      change range (f ∘ φ) = _
      rw [range_comp, hrange]
    refine ⟨φ, ψ, hφ, (ψ.continuous.isClosedEmbedding hinj).isEmbedding, hrange, hψrange, ?_⟩
    let H : C(Circle × unitInterval, S) := ⟨fun w => ψ w.1, by fun_prop⟩
    exact ⟨H, fun w => hZ (hψrange ▸ mem_range_self w.1), fun _ => rfl, fun _ => rfl⟩
  · exact exists_circle_parameters_of_arc_fibre hF hline f hfibre hZ

end GraphMinor.GM12
