/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.Basic
public import LeanPool.ToposTheoreticBridges.Subpresheaf
public import Mathlib.CategoryTheory.Yoneda

/-!
# Boolean presheaf topoi and groupoids

A category is *Boolean* (`IsBooleanTopos`) when every subobject has a complement in the
subobject lattice. We prove:

* `isBooleanTopos_presheaf_iff_isGroupoid`: the presheaf topos `Cᵒᵖ ⥤ Type u` of a small
  category `C` is Boolean iff `C` is a groupoid;
* `isBooleanTopos_of_equivalence`: being Boolean is invariant under equivalence of categories;
* `isGroupoid_iff_of_moritaEquivalentCat`: hence being a groupoid is a Morita invariant.

Proof of the main equivalence. Subobjects of a presheaf are subpresheaves
(`Subfunctor.orderIsoSubobject`), whose lattice operations are objectwise.
If `C` is a groupoid, the objectwise set complement of a subpresheaf is again a subpresheaf
(`Subfunctor.compl`). Conversely, for `f : d ⟶ c`, the complement of the subpresheaf
`Subfunctor.range (yoneda.map f)` of `yoneda.obj c` (the maps factoring through `f`) is the
objectwise set complement; since it is stable under precomposition and does not contain `f`,
it does not contain `𝟙 c`, so `f` has a section. Every morphism having a section, every
morphism is an isomorphism.

The notion `IsBooleanTopos` is stated for any category with the instances needed for the
order on subobjects to be bounded, and its invariance under equivalences only uses these
instances (`isCompl_orderIso_apply_iff`, for bounded partial orders). We do not formalise
topoi or subobject classifiers here.
-/

@[expose] public section

namespace LeanPool.ToposTheoreticBridges

open CategoryTheory Limits

universe u

/-- A category whose subobjects form bounded orders is Boolean when every subobject has a
complement. -/
def IsBooleanTopos (E : Type*) [Category E] [HasInitial E] [InitialMonoClass E] : Prop :=
  ∀ (X : E) (A : Subobject X), ∃ B : Subobject X, IsCompl A B

section Equivalence

variable {E E' : Type*} [Category E] [Category E'] [HasInitial E] [InitialMonoClass E]
  [HasInitial E'] [InitialMonoClass E']

/-- Being Boolean is invariant under equivalence of categories. -/
theorem isBooleanTopos_of_equivalence (e : E ≌ E') (h : IsBooleanTopos E) :
    IsBooleanTopos E' := by
  intro Y A
  let o : Subobject (e.inverse.obj Y) ≃o Subobject Y :=
    (subobjectOrderIsoOfEquivalence e.symm Y).symm
  obtain ⟨B, hB⟩ := h _ (o.symm A)
  exact ⟨o B, by simpa using (isCompl_orderIso_apply_iff o).2 hB⟩

/-- Being Boolean is invariant under equivalence of categories. -/
theorem isBooleanTopos_congr (e : E ≌ E') : IsBooleanTopos E ↔ IsBooleanTopos E' :=
  ⟨isBooleanTopos_of_equivalence e, isBooleanTopos_of_equivalence e.symm⟩

end Equivalence

section Presheaf

variable {C : Type u} [SmallCategory C]

/-- If presheaves on `C` form a Boolean category, every morphism of `C` has a section. -/
theorem exists_section_of_isBooleanTopos (h : IsBooleanTopos (Cᵒᵖ ⥤ Type u)) {d c : C}
    (f : d ⟶ c) : ∃ s : c ⟶ d, s ≫ f = 𝟙 c := by
  obtain ⟨T, hT⟩ :=
    (Subfunctor.exists_isCompl_iff_subobject (Subfunctor.range (yoneda.map f))).2 (h _ _)
  have hT' := Subfunctor.isCompl_iff_forall.1 hT
  by_contra hs
  have hc : 𝟙 c ∈ T.obj (Opposite.op c) := by
    rw [← (hT' _).compl_eq]
    rintro ⟨s, hs'⟩
    exact hs ⟨s, hs'⟩
  have hf := T.map f.op hc
  rw [Set.mem_preimage, ← (hT' _).compl_eq] at hf
  exact hf ⟨𝟙 d, by simp⟩

/-- If every morphism of a category has a section, the category is a groupoid. -/
theorem isGroupoid_of_forall_exists_section
    (h : ∀ {d c : C} (f : d ⟶ c), ∃ s : c ⟶ d, s ≫ f = 𝟙 c) : IsGroupoid C where
  all_isIso f := by
    obtain ⟨s, hs⟩ := h f
    obtain ⟨t, ht⟩ := h s
    have htf : t = f := by
      rw [← Category.comp_id t, ← hs, ← Category.assoc, ht, Category.id_comp]
    exact ⟨⟨s, by rw [← htf, ht], hs⟩⟩

end Presheaf

/-- The presheaf topos of a small category `C` is Boolean iff `C` is a groupoid. -/
theorem isBooleanTopos_presheaf_iff_isGroupoid (C : Type u) [SmallCategory C] :
    IsBooleanTopos (Cᵒᵖ ⥤ Type u) ↔ IsGroupoid C := by
  constructor
  · intro h
    exact isGroupoid_of_forall_exists_section (exists_section_of_isBooleanTopos h)
  · intro _ X A
    have : IsGroupoid Cᵒᵖ := ⟨fun f => inferInstanceAs (IsIso f.unop.op)⟩
    obtain ⟨B, hB⟩ := (Subfunctor.exists_isCompl_iff_subobject
      ((Subfunctor.orderIsoSubobject X).symm A)).1
      ⟨_, Subfunctor.isCompl_compl _⟩
    exact ⟨B, by simpa using hB⟩

/-- Being a groupoid is invariant under Morita equivalence of small categories. -/
theorem isGroupoid_iff_of_moritaEquivalentCat {C D : Type u} [SmallCategory C]
    [SmallCategory D] (h : MoritaEquivalentCat C D) : IsGroupoid C ↔ IsGroupoid D := by
  obtain ⟨e⟩ := h
  rw [← isBooleanTopos_presheaf_iff_isGroupoid, ← isBooleanTopos_presheaf_iff_isGroupoid]
  exact isBooleanTopos_congr e

end LeanPool.ToposTheoreticBridges
