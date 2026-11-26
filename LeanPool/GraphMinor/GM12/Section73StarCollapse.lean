/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73ArcCollapse
public import LeanPool.GraphMinor.GM12.Section73CollapseComposition
public import LeanPool.GraphMinor.Surface.Defs

/-!
# Collapsing a finite star of arcs

The radial-star contraction in XII (7.3), page 261, collapses finitely
many lines whose only common point is the centre. Collapse the lines
one at a time. Earlier collapses remain injective on the next line,
so its image is still an arc. The exact fibre calculation shows that
the composite identifies precisely the whole star.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- Contract a finite star of lines to its centre while fixing a
closed set disjoint from the star. This supplies the topological
contraction used in XII (7.3), page 261. -/
theorem exists_star_collapse
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {E : Set ι} (hE : E.Finite)
    (L : ι → Set S) (v : S)
    (hlines : ∀ i ∈ E, ∃ u, IsLineWithEnds (L i) v u)
    (hmeet : ∀ i ∈ E, ∀ j ∈ E, i ≠ j → L i ∩ L j ⊆ {v})
    {F : Set S} (hF : IsClosed F)
    (havoid : Disjoint ({v} ∪ ⋃ i ∈ E, L i) F) :
    ∃ f : C(S, S), Function.Surjective f ∧ (∀ x ∈ F, f x = x) ∧
      (∀ x ∈ {v} ∪ ⋃ i ∈ E, L i, f x = v) ∧
      (∀ x y, f x = f y ↔ x = y ∨
        (x ∈ {v} ∪ ⋃ i ∈ E, L i) ∧ (y ∈ {v} ∪ ⋃ i ∈ E, L i)) := by
  classical
  revert hlines hmeet havoid
  induction E, hE using Set.Finite.induction_on with
  | empty =>
    intro _ _ _
    refine ⟨ContinuousMap.id S, Function.surjective_id, fun _ _ => rfl, ?_, ?_⟩
    · simp
    · intro x y
      simp only [ContinuousMap.id_apply, iUnion_false, mem_empty_iff_false,
        iUnion_empty, union_empty, mem_singleton_iff]
      exact ⟨Or.inl, fun h => h.elim id (fun h => h.1.trans h.2.symm)⟩
  | @insert i E hi hE ih =>
    intro hlines hmeet havoid
    let A : Set S := {v} ∪ ⋃ j ∈ E, L j
    have hA_sub : A ⊆ {v} ∪ ⋃ j ∈ insert i E, L j := by
      intro x hx
      rcases hx with hx | hx
      · exact Or.inl hx
      · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
        exact Or.inr (mem_iUnion₂.mpr ⟨j, Or.inr hj, hxj⟩)
    have hLi_sub : L i ⊆ {v} ∪ ⋃ j ∈ insert i E, L j := fun _ hx =>
      Or.inr (mem_iUnion₂.mpr ⟨i, Or.inl rfl, hx⟩)
    obtain ⟨f, hfs, hfix, hconst, hfibre⟩ := ih
      (fun j hj => hlines j (Or.inr hj))
      (fun j hj k hk hjk => hmeet j (Or.inr hj) k (Or.inr hk) hjk)
      (havoid.mono_left hA_sub)
    have hvA : v ∈ A := Or.inl rfl
    have hfv : f v = v := hconst v hvA
    have hcap : A ∩ L i ⊆ {v} := by
      rintro x ⟨hx, hxi⟩
      rcases hx with hx | hx
      · exact hx
      · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
        exact hmeet j (Or.inr hj) i (Or.inl rfl) (fun h => hi (h ▸ hj)) ⟨hxj, hxi⟩
    have hinj : InjOn f (L i) := by
      intro x hx y hy heq
      rcases (hfibre x y).mp heq with hxy | hAxy
      · exact hxy
      · exact (hcap ⟨hAxy.1, hx⟩).trans (hcap ⟨hAxy.2, hy⟩).symm
    obtain ⟨u, p, hp0, hp1⟩ := hlines i (Or.inl rfl)
    let a : unitInterval → S := fun t => f (p t).val
    have ha : IsArcMap a := ⟨f.continuous.comp (continuous_subtype_val.comp p.continuous),
      fun _ _ h => p.injective (Subtype.ext (hinj (p _).property (p _).property h))⟩
    have hrange : range a = f '' L i := by
      ext x
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨(p t).val, (p t).property, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨p.symm ⟨z, hz⟩, congrArg f (congrArg Subtype.val (p.apply_symm_apply ⟨z, hz⟩))⟩
    have himageavoid : Disjoint (range a) F := by
      rw [hrange]
      apply disjoint_left.mpr
      rintro y ⟨x, hx, hxy⟩ hyF
      have heq : f x = f y := hxy.trans (hfix y hyF).symm
      rcases (hfibre x y).mp heq with hxy' | hAxy
      · exact disjoint_left.mp havoid (hLi_sub (hxy' ▸ hx)) hyF
      · exact disjoint_left.mp havoid (hA_sub hAxy.2) hyF
    obtain ⟨g, hgs, hgfix, hgconst, hgfibre⟩ := exists_arc_collapse hS ha hF himageavoid
    have ha0 : a 0 = v := (congrArg f hp0).trans hfv
    have hvLi : v ∈ L i := hp0 ▸ (p 0).property
    have hvimage : v ∈ f '' L i := ⟨v, hvLi, hfv⟩
    have hgfibre' : ∀ x y, g x = g y ↔ x = y ∨ (x ∈ f '' L i ∧ y ∈ f '' L i) := by
      simpa only [hrange] using hgfibre
    obtain ⟨hcompconst, hcompfibre⟩ := collapse_image_composition_fibres hfibre hgfibre' hconst
      hvimage
    have hgv : g v = v := (hgconst v (hrange.symm ▸ hvimage)).trans ha0
    have hUnion : ({v} ∪ ⋃ j ∈ insert i E, L j) = A ∪ L i := by
      ext x
      simp only [A, mem_union, mem_singleton_iff, mem_iUnion, mem_insert_iff]
      constructor
      · rintro (hx | ⟨j, hj, hxj⟩)
        · exact Or.inl (Or.inl hx)
        · rcases hj with rfl | hj
          · exact Or.inr hxj
          · exact Or.inl (Or.inr ⟨j, hj, hxj⟩)
      · rintro ((hx | ⟨j, hj, hxj⟩) | hx)
        · exact Or.inl hx
        · exact Or.inr ⟨j, Or.inr hj, hxj⟩
        · exact Or.inr ⟨i, Or.inl rfl, hx⟩
    refine ⟨g.comp f, hgs.comp hfs, ?_, ?_, ?_⟩
    · intro x hx
      change g (f x) = x
      rw [hfix x hx, hgfix x hx]
    · intro x hx
      exact (hcompconst x (hUnion ▸ hx)).trans hgv
    · simpa only [hUnion, ContinuousMap.comp_apply] using hcompfibre

end GraphMinor.GM12
