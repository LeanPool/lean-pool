/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.LocallyPresentableCategories.Reflective
public import Mathlib.CategoryTheory.Limits.Indization.Category
public import Mathlib.CategoryTheory.Presentable.Finite
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# Finitely accessible categories are categories of ind-objects

We prove `isFinitelyAccessibleCategory_iff_exists_ind` (roadmap 1.5; Adámek–Rosický,
Theorem 2.26, at `λ = ℵ₀`): a category is finitely accessible iff it is equivalent to `Ind A` for
a small category `A`.

* Forward: for `C` finitely accessible and `A` a small model of its finitely presentable objects,
  the nerve `C ⥤ Aᵒᵖ ⥤ Type w` is fully faithful, takes values in ind-objects (every object is
  the filtered colimit of the finitely presentable objects over it, and the nerve preserves
  filtered colimits and restricts to the Yoneda embedding on `A`), and every ind-object
  `colim yoneda (F i)` is the nerve of `colim F i`.
* Backward: in `Ind A` the objects `Ind.yoneda a` are finitely presentable, as
  `Hom(Ind.yoneda a, -)` is evaluation at `a`, and every object is a filtered colimit of them
  (Mathlib's `Ind.colimitPresentationCompYoneda`).
-/

@[expose] public section

namespace LeanPool.LocallyPresentableCategories

open CategoryTheory Limits Opposite Cardinal

universe w v u

attribute [local instance] fact_isRegular_aleph0

section Nerve

variable {C : Type u} [Category.{v} C] [IsFinitelyAccessibleCategory.{w} C]

/-- The nerve of a finitely accessible category takes values in ind-objects. -/
theorem isIndObject_presentableNerve_obj (X : C) :
    IsIndObject ((presentableNerve C ℵ₀).obj X) := by
  let ι := presentableModelι C ℵ₀
  let e := equivSmallModel.{w} (CostructuredArrow ι X)
  have := IsCardinalFiltered.of_equivalence ℵ₀ e
  have : IsFiltered (SmallModel.{w} (CostructuredArrow ι X)) :=
    isFiltered_of_isCardinalFiltered _ ℵ₀
  have := isCardinalAccessible_presentableNerve C ℵ₀
  have : PreservesColimitsOfShape (CostructuredArrow ι X) (presentableNerve C ℵ₀) :=
    Functor.preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall _ ℵ₀ _
  let hc := (isColimitOfPreserves (presentableNerve C ℵ₀) (ι.denseAt X)).whiskerEquivalence e.symm
  let iso : e.inverse ⋙ CostructuredArrow.proj ι X ⋙ yoneda ≅
      e.symm.functor ⋙ (CostructuredArrow.proj ι X ⋙ ι) ⋙ presentableNerve C ℵ₀ :=
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (presentableModelιCompPresentableNerveIso C ℵ₀).symm)
  exact IsIndObject.mk (IndObjectPresentation.ofCocone (F := e.inverse ⋙ CostructuredArrow.proj ι X)
    _ ((IsColimit.precomposeHomEquiv iso _).symm hc))

/-- Every ind-object on the finitely presentable objects is the nerve of an object. -/
theorem exists_iso_presentableNerve_obj (P : (presentableModel C ℵ₀)ᵒᵖ ⥤ Type w)
    (hP : IsIndObject P) : ∃ X : C, Nonempty ((presentableNerve C ℵ₀).obj X ≅ P) := by
  let p := hP.presentation
  have : IsCardinalFiltered p.I ℵ₀ := (isCardinalFiltered_aleph0_iff _).2 inferInstance
  have : HasColimitsOfShape p.I C := HasCardinalFilteredColimits.hasColimitsOfShape C ℵ₀ p.I
  have := isCardinalAccessible_presentableNerve C ℵ₀
  have : PreservesColimitsOfShape p.I (presentableNerve C ℵ₀) :=
    Functor.preservesColimitsOfShape_of_isCardinalAccessible _ ℵ₀ _
  exact ⟨colimit (p.F ⋙ presentableModelι C ℵ₀), ⟨preservesColimitIso _ _ ≪≫
    HasColimit.isoOfNatIso (Functor.isoWhiskerLeft p.F
      (presentableModelιCompPresentableNerveIso C ℵ₀)) ≪≫
    IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) p.coconeIsColimit⟩⟩

variable (C) in
/-- A finitely accessible category is equivalent to the ind-objects on its finitely presentable
objects. -/
noncomputable def equivalenceInd : C ≌ Ind (presentableModel C ℵ₀) :=
  have : (ObjectProperty.lift _ (presentableNerve C ℵ₀) isIndObject_presentableNerve_obj ⋙
      ObjectProperty.ι _).Full := inferInstanceAs (presentableNerve C ℵ₀).Full
  have : (ObjectProperty.lift _ (presentableNerve C ℵ₀) isIndObject_presentableNerve_obj ⋙
      ObjectProperty.ι _).Faithful := inferInstanceAs (presentableNerve C ℵ₀).Faithful
  have : (ObjectProperty.lift _ (presentableNerve C ℵ₀) isIndObject_presentableNerve_obj).Full :=
    Functor.Full.of_comp_faithful _ (ObjectProperty.ι _)
  have : (ObjectProperty.lift _ (presentableNerve C ℵ₀)
      isIndObject_presentableNerve_obj).Faithful :=
    Functor.Faithful.of_comp _ (ObjectProperty.ι _)
  have : (ObjectProperty.lift _ (presentableNerve C ℵ₀) isIndObject_presentableNerve_obj).EssSurj :=
    ⟨fun P ↦ by
      obtain ⟨X, ⟨e⟩⟩ := exists_iso_presentableNerve_obj P.obj P.property
      exact ⟨X, ⟨(ObjectProperty.fullyFaithfulι _).preimageIso e⟩⟩⟩
  have : (ObjectProperty.lift _ (presentableNerve C ℵ₀)
      isIndObject_presentableNerve_obj).IsEquivalence := { }
  (ObjectProperty.lift _ (presentableNerve C ℵ₀)
    isIndObject_presentableNerve_obj).asEquivalence.trans (Ind.equivalence _).symm

end Nerve

section Ind

variable (A : Type w) [SmallCategory A]

/-- `Hom(Ind.yoneda a, -)` is evaluation at `a`. -/
noncomputable def coyonedaIndYonedaIso (a : A) :
    coyoneda.obj (op (Ind.yoneda.obj a)) ≅ Ind.inclusion A ⋙ (evaluation _ _).obj (op a) :=
  NatIso.ofComponents fun Y ↦ Equiv.toIso (Ind.inclusion.fullyFaithful.homEquiv.trans
    (((Ind.yonedaCompInclusion.app a).homCongr (Iso.refl _)).trans yonedaEquiv))

instance isFinitelyPresentable_indYoneda_obj (a : A) :
    IsCardinalPresentable (Ind.yoneda.obj a) (ℵ₀ : Cardinal.{w}) where
  preservesColimitOfShape J _ _ := by
    have : IsFiltered J := isFiltered_of_isCardinalFiltered J ℵ₀
    exact preservesColimitsOfShape_of_natIso (coyonedaIndYonedaIso A a).symm

/-- The objects `Ind.yoneda a` form a filtered generator of `Ind A` by finitely presentable
objects. -/
theorem isCardinalFilteredGenerator_ofObj_indYoneda :
    (ObjectProperty.ofObj (Ind.yoneda (C := A)).obj).IsCardinalFilteredGenerator
      (ℵ₀ : Cardinal.{w}) where
  le_isCardinalPresentable := by
    rintro _ ⟨a⟩
    exact isFinitelyPresentable_indYoneda_obj A a
  exists_colimitsOfShape X :=
    ⟨X.presentation.I, inferInstance, (isCardinalFiltered_aleph0_iff _).2 inferInstance,
      ⟨(ObjectProperty.ColimitOfShape.colimit (X.presentation.F ⋙ Ind.yoneda)
        (fun i ↦ ObjectProperty.ofObj_apply Ind.yoneda.obj _)).ofIso
          (Ind.colimitPresentationCompYoneda X)⟩⟩

/-- `Ind A` is finitely accessible. -/
instance isFinitelyAccessibleCategory_ind : IsFinitelyAccessibleCategory.{w} (Ind A) where
  toHasCardinalFilteredGenerator :=
    (isCardinalFilteredGenerator_ofObj_indYoneda A).hasCardinalFilteredGenerator
  toHasCardinalFilteredColimits :=
    HasCardinalFilteredColimits_iff_hasFilteredColimitsOfSize.2 inferInstance

/-- Roadmap 1.5. A category is finitely accessible iff it is equivalent to `Ind A` for a small
category `A` (Adámek–Rosický, Theorem 2.26, at `λ = ℵ₀`). -/
theorem isFinitelyAccessibleCategory_iff_exists_ind (C : Type u) [Category.{v} C] :
    IsFinitelyAccessibleCategory.{w} C ↔
      ∃ (A : Type w) (_ : SmallCategory A), Nonempty (C ≌ Ind A) := by
  constructor
  · intro
    exact ⟨_, inferInstance, ⟨equivalenceInd C⟩⟩
  · rintro ⟨A, _, ⟨e⟩⟩
    exact e.symm.isCardinalAccessibleCategory _

end Ind

end LeanPool.LocallyPresentableCategories
