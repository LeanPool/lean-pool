/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.CategoryTheory.Presentable.Dense
public import Mathlib.CategoryTheory.Presentable.Adjunction
public import Mathlib.CategoryTheory.Presentable.Presheaf
public import Mathlib.CategoryTheory.Presentable.Type
public import Mathlib.CategoryTheory.Functor.KanExtension.DenseIff
public import Mathlib.CategoryTheory.Functor.KanExtension.RestrictedYoneda
public import Mathlib.CategoryTheory.Monad.Limits

/-!
# Locally presentable categories are reflective in presheaf categories

Let `C` be a `κ`-accessible category. We choose a small model `presentableModel C κ`
of the full subcategory of `κ`-presentable objects, with its (dense) inclusion
`presentableModelι C κ` into `C`, and consider the nerve
`presentableNerve C κ : C ⥤ (presentableModel C κ)ᵒᵖ ⥤ Type w`, sending `X` to the presheaf of
maps from `κ`-presentable objects to `X`. We show:

* the nerve is fully faithful (density of the `κ`-presentable objects, Mathlib's
  `IsCardinalAccessibleCategory` instance of `Functor.IsDense`), preserves limits, and restricts
  to the Yoneda embedding on `presentableModel C κ`
  (`presentableModelιCompPresentableNerveIso`);
* it is `κ`-accessible (`isCardinalAccessible_presentableNerve`), since the evaluations of the
  nerve are the functors `Hom(a, -)` for `κ`-presentable `a`
  (`isCardinalAccessible_shrinkCoyoneda_obj`);
* when `C` is locally `κ`-presentable, it is a right adjoint, its left adjoint being the left Kan
  extension of the inclusion along the Yoneda embedding (`isRightAdjoint_presentableNerve`).

Consequences:

* Roadmap 1.1, `hasLimitsOfSize_of_isCardinalLocallyPresentable`: a locally presentable category
  is complete, being a reflective subcategory of a presheaf category;
* Roadmap 1.2, `isCardinalLocallyPresentable_iff_exists_reflective`: locally `κ`-presentable
  categories are exactly the full reflective subcategories of presheaf categories on small
  categories whose inclusion is `κ`-accessible (Adámek–Rosický, Theorem 1.46). The converse
  direction is Mathlib's `Adjunction.isCardinalLocallyPresentable`.
-/

@[expose] public section

namespace LeanPool.LocallyPresentableCategories

open CategoryTheory Limits Opposite

universe w v u

section ShrinkCoyoneda

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]

/-- The functor `Hom(X, -)`, with values in `Type w`, preserves `κ`-filtered colimits when `X` is
`κ`-presentable. -/
theorem isCardinalAccessible_shrinkCoyoneda_obj (X : C) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalPresentable X κ] : (shrinkCoyoneda.{w}.obj (op X)).IsCardinalAccessible κ where
  preservesColimitOfShape J _ _ := by
    have := preservesColimitsOfShape_of_isCardinalPresentable X κ J
    have := preservesColimitsOfShape_of_natIso (J := J)
      (shrinkCoyonedaObjCompUliftFunctorIso.{w} (op X)).symm
    exact preservesColimitsOfShape_of_reflects_of_preserves _ uliftFunctor.{v, w}

end ShrinkCoyoneda

variable (C : Type u) [Category.{v} C] (κ : Cardinal.{w}) [Fact κ.IsRegular]

section Accessible

variable [IsCardinalAccessibleCategory C κ]

/-- A small model of the full subcategory of `κ`-presentable objects of `C`. -/
abbrev presentableModel : Type w :=
  SmallModel.{w} (isCardinalPresentable C κ).FullSubcategory

/-- The inclusion of the small model of the `κ`-presentable objects into `C`. -/
noncomputable def presentableModelι : presentableModel C κ ⥤ C :=
  (equivSmallModel.{w} _).inverse ⋙ (isCardinalPresentable C κ).ι

instance : (presentableModelι C κ).IsDense := by
  dsimp [presentableModelι]
  infer_instance

instance : (presentableModelι C κ).Full := by
  dsimp [presentableModelι]
  infer_instance

instance : (presentableModelι C κ).Faithful := by
  dsimp [presentableModelι]
  infer_instance

instance isCardinalPresentable_presentableModelι_obj (a : presentableModel C κ) :
    IsCardinalPresentable ((presentableModelι C κ).obj a) κ :=
  ((equivSmallModel.{w} _).inverse.obj a).2

/-- The canonical diagram of `κ`-presentable objects over an object of `C` is `κ`-filtered. -/
instance isCardinalFiltered_costructuredArrow_presentableModelι (X : C) :
    IsCardinalFiltered (CostructuredArrow (presentableModelι C κ) X) κ :=
  IsCardinalFiltered.of_equivalence κ (CostructuredArrow.pre (equivSmallModel.{w} _).inverse
    (isCardinalPresentable C κ).ι X).asEquivalence.symm

/-- The nerve `C ⥤ (presentableModel C κ)ᵒᵖ ⥤ Type w` of a `κ`-accessible category,
sending `X` to the presheaf of maps from `κ`-presentable objects to `X`. It is fully faithful,
by density of the `κ`-presentable objects. -/
noncomputable abbrev presentableNerve : C ⥤ (presentableModel C κ)ᵒᵖ ⥤ Type w :=
  Presheaf.restrictedShrinkYoneda.{w} (presentableModelι C κ)

/-- The nerve restricted to the `κ`-presentable objects is the Yoneda embedding. -/
noncomputable def presentableModelιCompPresentableNerveIso :
    presentableModelι C κ ⋙ presentableNerve C κ ≅ yoneda :=
  (asIso (shrinkYonedaMap₂.{w} (presentableModelι C κ))).symm ≪≫ shrinkYonedaIsoYoneda

/-- The evaluation of the nerve at `a` is the functor `Hom(a, -)`. -/
noncomputable def presentableNerveCompEvaluationIso (a : presentableModel C κ) :
    presentableNerve C κ ⋙ (evaluation _ _).obj (op a) ≅
      shrinkCoyoneda.{w}.obj (op ((presentableModelι C κ).obj a)) :=
  Iso.refl _

/-- The nerve of a `κ`-accessible category preserves limits. -/
instance preservesLimitsOfSize_presentableNerve :
    PreservesLimitsOfSize.{w, w} (presentableNerve C κ) :=
  preservesLimits_of_evaluation _ fun a ↦
    preservesLimits_of_natIso (presentableNerveCompEvaluationIso C κ a.unop).symm

/-- The nerve of a `κ`-accessible category is `κ`-accessible. -/
theorem isCardinalAccessible_presentableNerve :
    (presentableNerve C κ).IsCardinalAccessible κ where
  preservesColimitOfShape J _ _ := by
    refine preservesColimitsOfShape_of_evaluation _ _ fun a ↦ ?_
    have := (isCardinalAccessible_shrinkCoyoneda_obj ((presentableModelι C κ).obj a.unop)
      κ).preservesColimitOfShape J
    exact preservesColimitsOfShape_of_natIso (presentableNerveCompEvaluationIso C κ a.unop).symm

end Accessible

variable [IsCardinalLocallyPresentable C κ]

/-- The nerve of a locally presentable category is a right adjoint. -/
theorem isRightAdjoint_presentableNerve : (presentableNerve C κ).IsRightAdjoint :=
  ⟨_, ⟨Presheaf.restrictedShrinkYonedaAdjunction
    (shrinkYoneda.{w}.leftKanExtensionUnit (presentableModelι C κ))⟩⟩

/-- The nerve exhibits a locally presentable category as a reflective subcategory of a presheaf
category. -/
noncomputable instance : Reflective (presentableNerve C κ) :=
  ⟨_, Presheaf.restrictedShrinkYonedaAdjunction
    (shrinkYoneda.{w}.leftKanExtensionUnit (presentableModelι C κ))⟩

/-- Roadmap 1.1. A locally `κ`-presentable category has all `w`-small limits (a consequence of
Adámek–Rosický, Theorem 1.46). -/
theorem hasLimitsOfSize_of_isCardinalLocallyPresentable (D : Type u) [Category.{v} D]
    (κ' : Cardinal.{w}) [Fact κ'.IsRegular] [IsCardinalLocallyPresentable D κ'] :
    HasLimitsOfSize.{w, w} D :=
  ⟨fun _ _ ↦ hasLimitsOfShape_of_reflective (presentableNerve D κ')⟩

/-- A locally presentable category has all `w`-small limits. -/
instance hasLimitsOfSize_of_isLocallyPresentable (D : Type u) [Category.{v} D]
    [IsLocallyPresentable.{w} D] : HasLimitsOfSize.{w, w} D := by
  obtain ⟨κ, _, _⟩ := IsLocallyPresentable.exists_cardinal.{w} D
  exact hasLimitsOfSize_of_isCardinalLocallyPresentable D κ

omit [IsCardinalLocallyPresentable C κ] in
/-- Roadmap 1.2. A category is locally `κ`-presentable iff it is (equivalent to) a full reflective
subcategory of a presheaf category on a small category, closed under `κ`-filtered colimits
(Adámek–Rosický, Theorem 1.46). -/
theorem isCardinalLocallyPresentable_iff_exists_reflective :
    IsCardinalLocallyPresentable C κ ↔
      ∃ (A : Type w) (_ : SmallCategory A) (G : C ⥤ (Aᵒᵖ ⥤ Type w)),
        G.Full ∧ G.Faithful ∧ G.IsRightAdjoint ∧ G.IsCardinalAccessible κ := by
  constructor
  · intro
    exact ⟨_, inferInstance, presentableNerve C κ, inferInstance, inferInstance,
      isRightAdjoint_presentableNerve C κ, isCardinalAccessible_presentableNerve C κ⟩
  · rintro ⟨A, _, G, _, _, _, _⟩
    exact (Adjunction.ofIsRightAdjoint G).isCardinalLocallyPresentable κ

end LeanPool.LocallyPresentableCategories
