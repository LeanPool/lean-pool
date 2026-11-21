/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.LocallyPresentableCategories.Models
public import Mathlib.CategoryTheory.Functor.KanExtension.DenseAtCoyoneda
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Recovering a theory from its models

Let `T` be a small category with `κ`-small limits. We prove
`nonempty_isCardinalPresentable_models_equivalence` (roadmap 3.3): the `κ`-presentable models of
`T` are the corepresentable ones, and they form a category equivalent to `Tᵒᵖ`.

* Corepresentable functors are models, and they are `κ`-presentable in `Models T κ`, since
  `Hom(T(t, -), M) = M t` and `κ`-filtered colimits of models are computed in `T ⥤ Type w`
  (Mathlib's `MorphismProperty.isCardinalAccessible_ι_isLocal`, with roadmap 3.1).
* A model `M` is the colimit of the corepresentables over the opposite of its category of
  elements, which is `κ`-filtered (`isCardinalFiltered_elements_op`: the limit of a `κ`-small
  diagram of elements carries the element glued from the family). If `M` is `κ`-presentable its
  identity factors through a corepresentable, so `M` is a retract of a corepresentable; as `T`
  has equalizers, its idempotents split, and `M` is corepresentable.
-/

@[expose] public section

namespace LeanPool.LocallyPresentableCategories

open CategoryTheory Limits Opposite

universe w

variable {T : Type w} [SmallCategory T] {κ : Cardinal.{w}} [Fact κ.IsRegular]

/-- If `T` has `κ`-small limits and `M : T ⥤ Type w` preserves them, the opposite of the
category of elements of `M` is `κ`-filtered. -/
theorem isCardinalFiltered_elements_op (hT : HasCardinalSmallLimits T κ) (M : T ⥤ Type w)
    (hM : PreservesCardinalSmallLimits M κ) : IsCardinalFiltered M.Elementsᵒᵖ κ where
  nonempty_cocone {K} _ F hK := by
    let G := F.leftOp ⋙ Functor.Elements.π M
    have hK' : HasCardinalLT (Arrow Kᵒᵖ) κ := (hasCardinalLT_arrow_op_iff K κ).2 hK
    have := hT Kᵒᵖ hK'
    have := hM Kᵒᵖ hK'
    let hc := isLimitOfPreserves M (limit.isLimit G)
    let s : (G ⋙ M).sections := ⟨fun k ↦ (F.obj k.unop).unop.val,
      fun {k k'} u ↦ (F.map u.unop).unop.map_val⟩
    let x := (Types.isLimitEquivSections hc).symm s
    have hx (k : Kᵒᵖ) : M.map (limit.π G k) x = (F.obj k.unop).unop.val := by
      simpa using Types.isLimitEquivSections_symm_apply hc s k
    exact ⟨{ pt := op (M.elementsMk _ x)
             ι := { app k := (Functor.Elements.homMk (limit.π G (op k)) (hx (op k))).op
                    naturality k k' u := Quiver.Hom.unop_inj (by
                      ext
                      have := limit.w G u.op
                      simp only [Functor.const_obj_obj, Functor.const_obj_map, unop_comp,
                        unop_id, Category.id_comp, Functor.Elements.comp_hom] at this ⊢
                      exact this) } }⟩

variable (T κ)

/-- `κ`-filtered colimits of models are computed in `T ⥤ Type w`. -/
theorem isCardinalAccessible_ι_cardinalContinuous :
    (cardinalContinuous T κ).ι.IsCardinalAccessible κ := by
  obtain ⟨W, _, hW, h⟩ := exists_isLocal_eq_cardinalContinuous T κ
  rw [← h]
  exact MorphismProperty.isCardinalAccessible_ι_isLocal W κ hW

/-- The corepresentable models `T(t, -)`. -/
noncomputable def coyonedaModels : Tᵒᵖ ⥤ Models T κ :=
  (cardinalContinuous T κ).lift shrinkCoyoneda.{w} (fun _ _ _ _ ↦ inferInstance)

instance : (coyonedaModels T κ).Full :=
  have : (coyonedaModels T κ ⋙ ObjectProperty.ι _).Full :=
    inferInstanceAs (shrinkCoyoneda.{w} (C := T)).Full
  Functor.Full.of_comp_faithful _ (ObjectProperty.ι _)

instance : (coyonedaModels T κ).Faithful :=
  have : (coyonedaModels T κ ⋙ ObjectProperty.ι _).Faithful :=
    inferInstanceAs (shrinkCoyoneda.{w} (C := T)).Faithful
  Functor.Faithful.of_comp _ (ObjectProperty.ι _)

/-- `Hom(T(t, -), M)` is `M t`. -/
noncomputable def coyonedaCoyonedaModelsIso (t : Tᵒᵖ) :
    coyoneda.obj (op ((coyonedaModels T κ).obj t)) ≅
      (cardinalContinuous T κ).ι ⋙ (evaluation T (Type w)).obj t.unop :=
  NatIso.ofComponents fun M ↦ Equiv.toIso
    ((ObjectProperty.fullyFaithfulι _).homEquiv.trans shrinkCoyonedaEquiv)

/-- The corepresentable models are `κ`-presentable. -/
instance isCardinalPresentable_coyonedaModels_obj (t : Tᵒᵖ) :
    IsCardinalPresentable ((coyonedaModels T κ).obj t) κ where
  preservesColimitOfShape J _ _ := by
    have := (isCardinalAccessible_ι_cardinalContinuous T κ).preservesColimitOfShape J
    exact preservesColimitsOfShape_of_natIso (coyonedaCoyonedaModelsIso T κ t).symm

variable {T κ}

/-- A model as a cocone, in `Models T κ`, over the corepresentables indexed by the opposite of
its category of elements. -/
noncomputable def modelsCocone (M : Models T κ) :
    Cocone ((Functor.Elements.π M.obj).op ⋙ coyonedaModels T κ) where
  pt := M
  ι :=
    { app e := ObjectProperty.homMk ((Functor.Elements.shrinkCoyonedaCocone M.obj).ι.app e)
      naturality e e' f := by
        ext : 1
        exact (Functor.Elements.shrinkCoyonedaCocone M.obj).ι.naturality f }

/-- A model is the colimit of the corepresentables over its elements. -/
noncomputable def isColimitModelsCocone (M : Models T κ) : IsColimit (modelsCocone M) :=
  isColimitOfReflects (ObjectProperty.ι _)
    (Functor.Elements.isColimitShrinkCoyonedaCocone.{w} M.obj)

/-- A `κ`-presentable model is corepresentable. -/
theorem exists_iso_coyonedaModels_obj (hT : HasCardinalSmallLimits T κ) (M : Models T κ)
    [IsCardinalPresentable M κ] : ∃ t : Tᵒᵖ, Nonempty ((coyonedaModels T κ).obj t ≅ M) := by
  have := isCardinalFiltered_elements_op hT M.obj M.property
  obtain ⟨e, i, hi⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ
    (isColimitModelsCocone M) (𝟙 M)
  let Y := coyonedaModels T κ
  let r : Y.obj (op e.unop.obj) ⟶ M := (modelsCocone M).ι.app e
  let t := op e.unop.obj
  have hi' : i ≫ r = 𝟙 M := hi
  obtain ⟨g, hg⟩ := Y.map_surjective (r ≫ i)
  have hgg : g ≫ g = g := Y.map_injective (by
    rw [Y.map_comp, hg, Category.assoc, reassoc_of% hi'])
  have : HasLimitsOfShape (ULiftHom.{w} (ULift.{w} WalkingParallelPair)) T :=
    hT _ (hasCardinalLT_of_finite _ κ (Cardinal.IsRegular.aleph0_le Fact.out))
  have : HasLimitsOfShape WalkingParallelPair T := hasLimitsOfShape_of_equivalence
    (ULiftHomULiftCategory.equiv.{w, w} WalkingParallelPair).symm
  have : IsIdempotentComplete T :=
    (Idempotents.isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent T).2
      (fun _ _ _ ↦ inferInstance)
  obtain ⟨s, a, b, hab, hba⟩ := IsIdempotentComplete.idempotents_split t g hgg
  refine ⟨s, ⟨{ hom := Y.map a ≫ r, inv := i ≫ Y.map b, hom_inv_id := ?_, inv_hom_id := ?_ }⟩⟩
  · rw [Category.assoc, ← Category.assoc r, ← hg, ← hba, ← Y.map_comp, ← Y.map_comp,
      show a ≫ (b ≫ a) ≫ b = 𝟙 s by simp [hab], Y.map_id]
  · rw [Category.assoc, ← Category.assoc (Y.map b), ← Y.map_comp, hba, hg, Category.assoc,
      reassoc_of% hi', hi']

/-- Roadmap 3.3. For `T` with `κ`-small limits, the `κ`-presentable models are the corepresentable
ones, and they form a category equivalent to `Tᵒᵖ` (Gabriel–Ulmer 1971; compare the proof of
Lack–Rosický, Lemma 4.19). -/
theorem nonempty_isCardinalPresentable_models_equivalence (T : Type w) [SmallCategory T]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] (hT : HasCardinalSmallLimits T κ) :
    Nonempty ((isCardinalPresentable (Models T κ) κ).FullSubcategory ≌ Tᵒᵖ) := by
  let L := (isCardinalPresentable (Models T κ) κ).lift (coyonedaModels T κ)
    (fun t ↦ isCardinalPresentable_coyonedaModels_obj T κ t)
  have : (L ⋙ ObjectProperty.ι _).Full := inferInstanceAs (coyonedaModels T κ).Full
  have : (L ⋙ ObjectProperty.ι _).Faithful := inferInstanceAs (coyonedaModels T κ).Faithful
  have : L.Full := Functor.Full.of_comp_faithful _ (ObjectProperty.ι _)
  have : L.Faithful := Functor.Faithful.of_comp _ (ObjectProperty.ι _)
  have : L.EssSurj := ⟨fun M ↦ by
    have : IsCardinalPresentable M.obj κ := M.property
    obtain ⟨t, ⟨e⟩⟩ := exists_iso_coyonedaModels_obj hT M.obj
    exact ⟨t, ⟨(ObjectProperty.fullyFaithfulι _).preimageIso e⟩⟩⟩
  have : L.IsEquivalence := { }
  exact ⟨L.asEquivalence.symm⟩

end LeanPool.LocallyPresentableCategories
