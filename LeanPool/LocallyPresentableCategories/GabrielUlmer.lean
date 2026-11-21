/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.LocallyPresentableCategories.Models
public import LeanPool.LocallyPresentableCategories.Reflective
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.CategoryTheory.Presentable.Limits

/-!
# Gabriel–Ulmer duality on objects

* `isCardinalFiltered_costructuredArrow_yoneda`: if `A` is small with `κ`-small colimits and
  `P : Aᵒᵖ ⥤ Type w` sends them to limits, the category of elements of `P` is `κ`-filtered (the
  colimit of a `κ`-small diagram of elements carries the element glued from the family).
* `isCardinalLocallyPresentable_iff_exists_models` (roadmap 3.2; Gabriel–Ulmer, Lack–Rosický,
  Theorem 5.4): a category is locally `κ`-presentable iff it is equivalent to the category of
  models of a small category with `κ`-small limits. For `C` locally `κ`-presentable, take `T` the
  opposite of a small model `A` of the `κ`-presentable objects; these are closed under `κ`-small
  colimits, and the nerve `C ⥤ Aᵒᵖ ⥤ Type w` is fully faithful and lands in the models. A model
  `P` is the `κ`-filtered colimit of the representables over it, hence the nerve of the colimit
  of the corresponding `κ`-presentable objects, the nerve being `κ`-accessible.
* `isCardinalLocallyPresentable_iff_exists_isLocal` (roadmap 2.1): locally `κ`-presentable
  categories are the small-orthogonality classes of presheaves for maps between
  `κ`-presentable presheaves, from 3.2, 3.1 and Mathlib's orthogonal-reflection theorem.
-/

@[expose] public section

namespace LeanPool.LocallyPresentableCategories

open CategoryTheory Limits Opposite

universe w v u

section Elements

variable {A : Type w} [SmallCategory A] {κ : Cardinal.{w}} [Fact κ.IsRegular]

/-- If `A` has `κ`-small colimits and `P : Aᵒᵖ ⥤ Type w` sends them to limits, the category of
elements of `P` is `κ`-filtered. -/
theorem isCardinalFiltered_costructuredArrow_yoneda
    (hA : ∀ (J : Type w) [SmallCategory J], HasCardinalLT (Arrow J) κ → HasColimitsOfShape J A)
    (P : Aᵒᵖ ⥤ Type w) (hP : PreservesCardinalSmallLimits P κ) :
    IsCardinalFiltered (CostructuredArrow yoneda P) κ where
  nonempty_cocone {K} _ F hK := by
    let G := F ⋙ CostructuredArrow.proj yoneda P
    have := hA K hK
    have := hP Kᵒᵖ ((hasCardinalLT_arrow_op_iff K κ).2 hK)
    let hc := isLimitOfPreserves P (colimit.isColimit G).op
    let y (k : Kᵒᵖ) : P.obj (op (G.obj k.unop)) := yonedaEquiv (F.obj k.unop).hom
    let s : (G.op ⋙ P).sections := ⟨y, fun {k k'} u ↦ by
      change P.map (G.map u.unop).op _ = _
      rw [yonedaEquiv_naturality]
      exact congrArg yonedaEquiv (CostructuredArrow.w (F.map u.unop))⟩
    let x := (Types.isLimitEquivSections hc).symm s
    have hx (k : K) : P.map (colimit.ι G k).op x = yonedaEquiv (F.obj k).hom := by
      simpa using Types.isLimitEquivSections_symm_apply hc s (op k)
    exact ⟨{ pt := CostructuredArrow.mk (yonedaEquiv.symm x)
             ι := { app k := CostructuredArrow.homMk (colimit.ι G k) (yonedaEquiv.injective (by
                      rw [← yonedaEquiv_naturality]
                      simpa using hx k))
                    naturality k k' u := by
                      ext
                      simp only [Functor.const_obj_obj, Functor.const_obj_map,
                        Category.comp_id, CostructuredArrow.comp_left,
                        CostructuredArrow.homMk_left]
                      exact colimit.w G u } }⟩

end Elements

section GabrielUlmer

variable (C : Type u) [Category.{v} C] (κ : Cardinal.{w}) [Fact κ.IsRegular]
  [IsCardinalLocallyPresentable C κ]

/-- The small model of the `κ`-presentable objects has `κ`-small colimits. -/
theorem hasColimitsOfShape_presentableModel (J : Type w) [SmallCategory J]
    (hJ : HasCardinalLT (Arrow J) κ) : HasColimitsOfShape J (presentableModel C κ) := by
  have := isClosedUnderColimitsOfShape_isCardinalPresentable C hJ
  exact Adjunction.hasColimitsOfShape_of_equivalence (equivSmallModel.{w} _).inverse

/-- The inclusion of the `κ`-presentable objects preserves `κ`-small colimits. -/
theorem preservesColimitsOfShape_presentableModelι (J : Type w) [SmallCategory J]
    (hJ : HasCardinalLT (Arrow J) κ) : PreservesColimitsOfShape J (presentableModelι C κ) := by
  have := isClosedUnderColimitsOfShape_isCardinalPresentable C hJ
  exact comp_preservesColimitsOfShape _ _

/-- The nerve of an object is a model of the opposite of the `κ`-presentable objects. -/
theorem cardinalContinuous_presentableNerve_obj (X : C) :
    cardinalContinuous (presentableModel C κ)ᵒᵖ κ ((presentableNerve C κ).obj X) := by
  intro J _ hJ
  have := preservesColimitsOfShape_presentableModelι C κ Jᵒᵖ
    ((hasCardinalLT_arrow_op_iff J κ).2 hJ)
  have := preservesLimitsOfShape_op (J := J) (presentableModelι C κ)
  change PreservesLimitsOfShape J ((presentableModelι C κ).op ⋙ shrinkYoneda.{w}.obj X)
  infer_instance

/-- Every model of the opposite of the `κ`-presentable objects is a nerve. -/
theorem exists_iso_presentableNerve_obj_of_cardinalContinuous
    (P : (presentableModel C κ)ᵒᵖ ⥤ Type w) (hP : cardinalContinuous _ κ P) :
    ∃ X : C, Nonempty ((presentableNerve C κ).obj X ≅ P) := by
  have := isCardinalFiltered_costructuredArrow_yoneda
    (hasColimitsOfShape_presentableModel C κ) P hP
  have := isCardinalAccessible_presentableNerve C κ
  have : PreservesColimitsOfShape (CostructuredArrow yoneda P) (presentableNerve C κ) :=
    Functor.preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall _ κ _
  exact ⟨colimit (CostructuredArrow.proj yoneda P ⋙ presentableModelι C κ),
    ⟨preservesColimitIso _ _ ≪≫ HasColimit.isoOfNatIso
      (Functor.isoWhiskerLeft (CostructuredArrow.proj yoneda P)
        (presentableModelιCompPresentableNerveIso C κ)) ≪≫
      IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (denseAtYoneda P)⟩⟩

/-- Gabriel–Ulmer: a locally `κ`-presentable category is equivalent to the models of the
opposite of its `κ`-presentable objects. -/
noncomputable def equivalenceModels : C ≌ Models (presentableModel C κ)ᵒᵖ κ :=
  let L := ObjectProperty.lift _ (presentableNerve C κ)
    (cardinalContinuous_presentableNerve_obj C κ)
  have : (L ⋙ ObjectProperty.ι _).Full := inferInstanceAs (presentableNerve C κ).Full
  have : (L ⋙ ObjectProperty.ι _).Faithful := inferInstanceAs (presentableNerve C κ).Faithful
  have : L.Full := Functor.Full.of_comp_faithful _ (ObjectProperty.ι _)
  have : L.Faithful := Functor.Faithful.of_comp _ (ObjectProperty.ι _)
  have : L.EssSurj := ⟨fun P ↦ by
    obtain ⟨X, ⟨e⟩⟩ := exists_iso_presentableNerve_obj_of_cardinalContinuous C κ P.obj P.property
    exact ⟨X, ⟨(ObjectProperty.fullyFaithfulι _).preimageIso e⟩⟩⟩
  have : L.IsEquivalence := { }
  L.asEquivalence

end GabrielUlmer

/-- Roadmap 3.2. Gabriel–Ulmer: a category is locally `κ`-presentable iff it is equivalent to the
models of a small category with `κ`-small limits (Lack–Rosický, Theorem 5.4; Adámek–Rosický,
Theorem 1.46). -/
theorem isCardinalLocallyPresentable_iff_exists_models (C : Type u) [Category.{v} C]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    IsCardinalLocallyPresentable C κ ↔
      ∃ (T : Type w) (_ : SmallCategory T),
        HasCardinalSmallLimits T κ ∧ Nonempty (C ≌ Models T κ) := by
  constructor
  · intro
    refine ⟨_, inferInstance, fun J _ hJ ↦ ?_, ⟨equivalenceModels C κ⟩⟩
    have := hasColimitsOfShape_presentableModel C κ Jᵒᵖ ((hasCardinalLT_arrow_op_iff J κ).2 hJ)
    exact hasLimitsOfShape_op_of_hasColimitsOfShape
  · rintro ⟨T, _, _, ⟨e⟩⟩
    have := isCardinalLocallyPresentable_models T κ
    exact e.symm.isCardinalLocallyPresentable κ

/-- Roadmap 2.1. A category is locally `κ`-presentable iff it is equivalent to the full
subcategory of `W`-local presheaves on a small category, for a small class `W` of maps between
`κ`-presentable presheaves (Adámek–Rosický, Theorem 1.46; Kelly, Theorems 6.5 and 6.11). -/
theorem isCardinalLocallyPresentable_iff_exists_isLocal (C : Type u) [Category.{v} C]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    IsCardinalLocallyPresentable C κ ↔
      ∃ (A : Type w) (_ : SmallCategory A) (W : MorphismProperty (Aᵒᵖ ⥤ Type w))
        (_ : MorphismProperty.IsSmall.{w} W),
        (∀ ⦃X Y : Aᵒᵖ ⥤ Type w⦄ (f : X ⟶ Y), W f →
          IsCardinalPresentable X κ ∧ IsCardinalPresentable Y κ) ∧
        Nonempty (C ≌ W.isLocal.FullSubcategory) := by
  constructor
  · intro
    obtain ⟨W, _, hW, hW'⟩ := exists_isLocal_eq_cardinalContinuous (presentableModel C κ)ᵒᵖ κ
    refine ⟨presentableModel C κ, inferInstance, W, inferInstance, hW, ?_⟩
    rw [hW']
    exact ⟨equivalenceModels C κ⟩
  · rintro ⟨A, _, W, _, hW, ⟨e⟩⟩
    have := MorphismProperty.isLocallyPresentable_isLocal W κ hW
    exact e.symm.isCardinalLocallyPresentable κ

end LeanPool.LocallyPresentableCategories
