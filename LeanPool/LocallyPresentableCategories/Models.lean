/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.LocallyPresentableCategories.Basic
public import LeanPool.LocallyPresentableCategories.Orthogonality
public import Mathlib.CategoryTheory.SmallRepresentatives
public import Mathlib.CategoryTheory.Limits.Sifted

/-!
# Models of limit theories form locally presentable categories

For a small category `T` and a regular cardinal `κ`, the models of `T` are the functors
`T ⥤ Type w` preserving `κ`-small limits. We prove:

* `exists_isLocal_eq_cardinalContinuous` (roadmap 3.1): the models form a small-orthogonality
  class in `T ⥤ Type w`, for maps between `κ`-presentable functors (Kelly, Theorem 6.11);
* `isCardinalLocallyPresentable_models` (roadmap 3.1): the models form a locally
  `κ`-presentable category;
* `isRightAdjoint_ι_dModels` (roadmap 5.1): for a small family `D` of small shapes, the functors
  `R ⥤ Type w` preserving limits of the shapes `D a` form a reflective, locally presentable
  subcategory of `R ⥤ Type w`;
* `isLocallyFinitelyPresentable_algebras` (roadmap 4.1): the finite-product-preserving functors
  `T ⥤ Type w` (the algebras of `T`) form a locally finitely presentable category;
* `preservesColimitsOfShape_algebras_ι` (roadmap 4.2): sifted colimits of algebras are computed
  in `T ⥤ Type w`, by Mathlib's theorem that sifted colimits commute with finite products in
  types (`IsSifted.colim_preservesFiniteProducts_of_isSifted`).

All of them are obtained from `LeanPool.LocallyPresentableCategories.Orthogonality`, which
expresses limit preservation as orthogonality to maps between presentable functors, and from
Mathlib's orthogonal-reflection theorem `MorphismProperty.isLocallyPresentable_isLocal`.
To reduce the (large) class of `κ`-small shapes to a small one we use Mathlib's representative
family `SmallCategoryCardinalLT.categoryFamily`.
-/

@[expose] public section

namespace LeanPool.LocallyPresentableCategories

open CategoryTheory Limits Opposite

universe w

section Models

variable (T : Type w) [SmallCategory T] (κ : Cardinal.{w})

/-- The models of `T` in `Type w`: the functors `T ⥤ Type w` preserving `κ`-small limits. -/
def cardinalContinuous : ObjectProperty (T ⥤ Type w) :=
  fun F ↦ PreservesCardinalSmallLimits F κ

/-- The category `Mod_κ T` of models of `T`. -/
abbrev Models : Type (w + 1) :=
  (cardinalContinuous T κ).FullSubcategory

/-- Preserving `κ`-small limits amounts to preserving the limits of the shapes of Mathlib's
representative family of `κ`-small categories. -/
lemma cardinalContinuous_eq :
    cardinalContinuous T κ =
      preservesLimitsOfShapes (SmallCategoryCardinalLT.categoryFamily κ) T := by
  ext F
  constructor
  · intro h S
    exact h _ (SmallCategoryCardinalLT.hasCardinalLT κ S)
  · intro h J _ hJ
    obtain ⟨S, ⟨e⟩⟩ := SmallCategoryCardinalLT.exists_equivalence κ J hJ
    have := h S
    exact preservesLimitsOfShape_of_equiv e F

variable [Fact κ.IsRegular]

/-- Roadmap 3.1. The models of a small `T` form a small-orthogonality class in `T ⥤ Type w`, for
maps between `κ`-presentable functors (Kelly, Theorem 6.11). -/
theorem exists_isLocal_eq_cardinalContinuous :
    ∃ (W : MorphismProperty (T ⥤ Type w)) (_ : MorphismProperty.IsSmall.{w} W),
      (∀ ⦃X Y : T ⥤ Type w⦄ (f : X ⟶ Y), W f →
        IsCardinalPresentable X κ ∧ IsCardinalPresentable Y κ) ∧
      W.isLocal = cardinalContinuous T κ :=
  ⟨limitComparisons (SmallCategoryCardinalLT.categoryFamily κ) T, inferInstance,
    isCardinalPresentable_limitComparisons κ (SmallCategoryCardinalLT.hasCardinalLT κ),
    by rw [isLocal_limitComparisons, cardinalContinuous_eq]⟩

/-- Roadmap 3.1. The models of a small `T` form a locally `κ`-presentable category (Kelly,
Theorem 6.11). -/
theorem isCardinalLocallyPresentable_models :
    IsCardinalLocallyPresentable (Models T κ) κ := by
  change IsCardinalLocallyPresentable (cardinalContinuous T κ).FullSubcategory κ
  rw [cardinalContinuous_eq]
  exact isCardinalLocallyPresentable_preservesLimitsOfShapes κ
    (SmallCategoryCardinalLT.hasCardinalLT κ)

/-- The inclusion of the models of `T` into `T ⥤ Type w` is a right adjoint. -/
theorem isRightAdjoint_ι_cardinalContinuous :
    (cardinalContinuous T κ).ι.IsRightAdjoint := by
  rw [cardinalContinuous_eq]
  exact isRightAdjoint_ι_preservesLimitsOfShapes κ (SmallCategoryCardinalLT.hasCardinalLT κ)

end Models

section DLimits

variable {α : Type w} (D : α → Type w) [∀ a, SmallCategory (D a)]

/-- A functor is a `D`-functor: it preserves limits of every shape `D a`. -/
def PreservesDLimits {X : Type*} [Category* X] {Y : Type*} [Category* Y] (F : X ⥤ Y) : Prop :=
  ∀ a, PreservesLimitsOfShape (D a) F

/-- The `D`-functors `X ⥤ Y`, as a property of objects of the functor category. -/
def dContinuous (X : Type*) [Category* X] (Y : Type*) [Category* Y] : ObjectProperty (X ⥤ Y) :=
  fun F ↦ PreservesDLimits D F

/-- Roadmap 5.1. The models in `Type w` of a small `R` (its `D`-functors to `Type w`) form a
reflective, locally presentable subcategory of `R ⥤ Type w` (Kelly, Theorem 6.11). -/
theorem isRightAdjoint_ι_dModels (R : Type w) [SmallCategory R] :
    (dContinuous D R (Type w)).ι.IsRightAdjoint ∧
      IsLocallyPresentable.{w} (dContinuous D R (Type w)).FullSubcategory := by
  obtain ⟨κ, hκ, hD⟩ := HasCardinalLT.exists_regular_cardinal_forall.{w}
    (fun a ↦ Arrow (D a))
  have : Fact κ.IsRegular := ⟨hκ⟩
  exact ⟨isRightAdjoint_ι_preservesLimitsOfShapes (T := R) κ hD,
    ⟨κ, inferInstance, isCardinalLocallyPresentable_preservesLimitsOfShapes (T := R) κ hD⟩⟩

end DLimits

section Algebras

variable (T : Type w) [SmallCategory T]

/-- The algebras of `T`: functors `T ⥤ Type w` preserving finite products. -/
def productPreserving : ObjectProperty (T ⥤ Type w) :=
  fun F ↦ PreservesFiniteProducts F

/-- The category `Alg T` of algebras of `T`. -/
abbrev Algebras : Type (w + 1) :=
  (productPreserving T).FullSubcategory

/-- Finite discrete shapes in `Type w`. -/
abbrev finiteDiscreteShapes (n : ULift.{w} ℕ) : Type w :=
  Discrete (ULift.{w} (Fin n.down))

lemma productPreserving_eq :
    productPreserving T = preservesLimitsOfShapes finiteDiscreteShapes T := by
  ext F
  constructor
  · intro h n
    have := h.preserves n.down
    exact preservesLimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift.symm) F
  · intro h
    exact ⟨fun n ↦ by
      have := h ⟨n⟩
      exact preservesLimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) F⟩

open Cardinal in
/-- Roadmap 4.1. The algebras of a small `T` form a locally finitely presentable category (the
case of finite discrete cones in Kelly, Theorem 6.11). -/
theorem isLocallyFinitelyPresentable_algebras :
    IsLocallyFinitelyPresentable.{w} (Algebras T) := by
  have : Fact (aleph0.{w}).IsRegular := fact_isRegular_aleph0
  change IsCardinalLocallyPresentable (productPreserving T).FullSubcategory ℵ₀
  rw [productPreserving_eq]
  exact isCardinalLocallyPresentable_preservesLimitsOfShapes ℵ₀
    (fun n ↦ by rw [hasCardinalLT_aleph0_iff]; infer_instance)

/-- A sifted colimit, in `T ⥤ Type w`, of finite-product-preserving functors preserves finite
products. -/
instance isClosedUnderColimitsOfShape_productPreserving (J : Type w) [SmallCategory J]
    [IsSifted J] : (productPreserving T).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro X ⟨p⟩
    have hF : PreservesFiniteProducts p.diag.flip := ⟨fun n ↦ by
      refine preservesLimitsOfShape_of_evaluation _ _ fun j ↦ ?_
      have := (p.prop_diag_obj j).preserves n
      exact preservesLimitsOfShape_of_natIso (flipCompEvaluation p.diag j).symm⟩
    let e : p.diag.flip ⋙ colim ≅ X :=
      (colimitIsoFlipCompColim p.diag).symm ≪≫
        (colimit.isColimit _).coconePointUniqueUpToIso p.isColimit
    exact ⟨fun n ↦ preservesLimitsOfShape_of_natIso e⟩

/-- Roadmap 4.2. Sifted colimits of algebras are computed in `T ⥤ Type w` (sifted colimits commute
with finite products in types; Lack–Rosický, §3). -/
theorem preservesColimitsOfShape_algebras_ι (J : Type w) [SmallCategory J] [IsSifted J] :
    PreservesColimitsOfShape J (productPreserving T).ι :=
  inferInstance

end Algebras

end LeanPool.LocallyPresentableCategories
