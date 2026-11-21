/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.LocallyPresentableCategories.AdjointFunctor
public import LeanPool.LocallyPresentableCategories.Theory

/-!
# Algebraic functors

For a morphism of theories `G : T ⥤ T'` (a functor preserving `κ`-small limits), restriction
along `G` is a functor `restrict G hG : Models T' κ ⥤ Models T κ`. We prove
`restrict_isRightAdjoint` (roadmap 3.4): it is a `κ`-accessible right adjoint. Both properties
are checked after composing with the inclusion `Models T κ ⥤ T ⥤ Type w`, which is fully
faithful, preserves limits and `κ`-filtered colimits; the adjoint functor theorem between
locally presentable categories (roadmap 1.4) then gives the left adjoint.

Conversely (`exists_iso_restrict`, roadmap 3.4), a `κ`-accessible right adjoint
`U : Models T' κ ⥤ Models T κ`, with `T'` having `κ`-small limits, is isomorphic to restriction
along some `G : T ⥤ T'`. Its left adjoint `F` preserves `κ`-presentable objects, so it sends
the corepresentable `T(t, -)` to a corepresentable `T'(G t, -)` (roadmap 3.3); then
`(U M) t = Hom(T(t, -), U M) = Hom(F T(t, -), M) = M (G t)`, and `G` preserves `κ`-small limits
because every `T'(t', G -) = U (T'(t', -))` does. The hypothesis of the roadmap that `T` has
`κ`-small limits is not needed.
-/

@[expose] public section

namespace LeanPool.LocallyPresentableCategories

open CategoryTheory Limits Opposite

universe w

section Whiskering

variable {T T' : Type w} [SmallCategory T] [SmallCategory T'] (G : T ⥤ T')

/-- Precomposition with `G` preserves colimits, as they are computed pointwise. -/
instance preservesColimitsOfShape_whiskeringLeft_obj (J : Type w) [SmallCategory J] :
    PreservesColimitsOfShape J ((Functor.whiskeringLeft T T' (Type w)).obj G) :=
  preservesColimitsOfShape_of_evaluation _ _ fun t ↦
    inferInstanceAs (PreservesColimitsOfShape J ((evaluation T' (Type w)).obj (G.obj t)))

/-- Precomposition with `G` preserves limits, as they are computed pointwise. -/
instance preservesLimitsOfSize_whiskeringLeft_obj :
    PreservesLimitsOfSize.{w, w} ((Functor.whiskeringLeft T T' (Type w)).obj G) :=
  preservesLimits_of_evaluation _ fun t ↦
    inferInstanceAs (PreservesLimitsOfSize.{w, w} ((evaluation T' (Type w)).obj (G.obj t)))

end Whiskering

/-- The algebraic functor `G^* : Mod_κ T' ⥤ Mod_κ T`, restriction along a morphism of theories
`G : T ⥤ T'`. -/
def restrict {T T' : Type w} [SmallCategory T] [SmallCategory T'] {κ : Cardinal.{w}}
    (G : T ⥤ T') (hG : PreservesCardinalSmallLimits G κ) : Models T' κ ⥤ Models T κ :=
  (cardinalContinuous T κ).lift
    ((cardinalContinuous T' κ).ι ⋙ (Functor.whiskeringLeft T T' (Type w)).obj G)
    (fun M J _ hJ ↦ by
      have := hG J hJ
      have := M.property J hJ
      exact comp_preservesLimitsOfShape G M.obj)

/-- Roadmap 3.4. An algebraic functor is a `κ`-accessible right adjoint (Lack–Rosický, §5.2). -/
theorem restrict_isRightAdjoint {T T' : Type w} [SmallCategory T] [SmallCategory T']
    {κ : Cardinal.{w}} [Fact κ.IsRegular] (G : T ⥤ T') (hG : PreservesCardinalSmallLimits G κ) :
    (restrict G hG).IsRightAdjoint ∧ (restrict G hG).IsCardinalAccessible κ := by
  have hacc : (restrict G hG).IsCardinalAccessible κ := ⟨fun J _ _ ↦ by
    have := (isCardinalAccessible_ι_cardinalContinuous T' κ).preservesColimitOfShape J
    have : PreservesColimitsOfShape J (restrict G hG ⋙ (cardinalContinuous T κ).ι) :=
      inferInstanceAs (PreservesColimitsOfShape J
        ((cardinalContinuous T' κ).ι ⋙ (Functor.whiskeringLeft T T' (Type w)).obj G))
    exact preservesColimitsOfShape_of_reflects_of_preserves _ (cardinalContinuous T κ).ι⟩
  have := isRightAdjoint_ι_cardinalContinuous T' κ
  have : PreservesLimitsOfSize.{w, w} (restrict G hG ⋙ (cardinalContinuous T κ).ι) :=
    inferInstanceAs (PreservesLimitsOfSize.{w, w}
      ((cardinalContinuous T' κ).ι ⋙ (Functor.whiskeringLeft T T' (Type w)).obj G))
  have : PreservesLimitsOfSize.{w, w} (restrict G hG) :=
    preservesLimits_of_reflects_of_preserves _ (cardinalContinuous T κ).ι
  have : IsLocallyPresentable.{w} (Models T κ) := ⟨κ, inferInstance,
    isCardinalLocallyPresentable_models T κ⟩
  have : IsLocallyPresentable.{w} (Models T' κ) := ⟨κ, inferInstance,
    isCardinalLocallyPresentable_models T' κ⟩
  exact ⟨(isRightAdjoint_iff _).2 ⟨inferInstance,
    Functor.isAccessible_of_isCardinalAccessible _ κ⟩, hacc⟩

section Converse

variable (T : Type w) [SmallCategory T] (κ : Cardinal.{w}) [Fact κ.IsRegular]

/-- A model `M` evaluated at `t` is `Hom(T(t, -), M)`. -/
noncomputable def modelsObjEquiv (M : Models T κ) (t : T) :
    M.obj.obj t ≃ ((coyonedaModels T κ).obj (op t) ⟶ M) :=
  shrinkCoyonedaEquiv.symm.trans ((ObjectProperty.fullyFaithfulι _).homEquiv
    (X := (coyonedaModels T κ).obj (op t)) (Y := M)).symm

/-- A model `M` evaluated at `t` is `Hom(T(t, -), M)`, naturally in `t` and `M`. -/
noncomputable def ιModelsIsoYoneda :
    (cardinalContinuous T κ).ι ≅
      yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (opOp T ⋙ (coyonedaModels T κ).op) :=
  NatIso.ofComponents (fun M ↦ NatIso.ofComponents (fun t ↦ Equiv.toIso
    (modelsObjEquiv T κ M t)) (fun f ↦ by
      ext x
      apply ObjectProperty.hom_ext
      change shrinkCoyonedaEquiv.symm (M.obj.map f x) =
        shrinkCoyoneda.map f.op ≫ shrinkCoyonedaEquiv.symm x
      exact shrinkCoyonedaEquiv_symm_map f x)) (fun φ ↦ by
      ext t x
      apply ObjectProperty.hom_ext
      change shrinkCoyonedaEquiv.symm (φ.hom.app t x) = shrinkCoyonedaEquiv.symm x ≫ φ.hom
      apply shrinkCoyonedaEquiv.injective
      rw [shrinkCoyonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply])

/-- Roadmap 3.4. Every `κ`-accessible right adjoint `Models T' κ ⥤ Models T κ`, where `T'` has
`κ`-small limits, is isomorphic to an algebraic functor (Gabriel–Ulmer 1971). The roadmap also
assumes that `T` has `κ`-small limits; this is not needed. -/
theorem exists_iso_restrict {T T' : Type w} [SmallCategory T] [SmallCategory T']
    {κ : Cardinal.{w}} [Fact κ.IsRegular] (hT' : HasCardinalSmallLimits T' κ)
    (U : Models T' κ ⥤ Models T κ) [U.IsRightAdjoint]
    [U.IsCardinalAccessible κ] :
    ∃ (G : T ⥤ T') (hG : PreservesCardinalSmallLimits G κ), Nonempty (U ≅ restrict G hG) := by
  let adj := Adjunction.ofIsRightAdjoint U
  let Y := coyonedaModels T κ
  let Y' := coyonedaModels T' κ
  have h (t : Tᵒᵖ) : Y'.essImage ((Y ⋙ U.leftAdjoint).obj t) := by
    have : IsCardinalPresentable ((Y ⋙ U.leftAdjoint).obj t) κ :=
      adj.isCardinalPresentable_leftAdjoint_obj κ (Y.obj t)
    obtain ⟨t', ⟨e⟩⟩ := exists_iso_coyonedaModels_obj hT' ((Y ⋙ U.leftAdjoint).obj t)
    exact ⟨t', ⟨e⟩⟩
  let Gop := Functor.essImage.liftFunctor (Y ⋙ U.leftAdjoint) Y' h
  let β : Gop ⋙ Y' ≅ Y ⋙ U.leftAdjoint := Functor.essImage.liftFunctorCompIso _ _ h
  let G : T ⥤ T' := Gop.unop
  let e₁ : U ⋙ (cardinalContinuous T κ).ι ≅
      yoneda ⋙ (Functor.whiskeringLeft _ _ (Type w)).obj (opOp T ⋙ (Y ⋙ U.leftAdjoint).op) :=
    Functor.isoWhiskerLeft U (ιModelsIsoYoneda T κ) ≪≫
      Functor.isoWhiskerRight adj.compYonedaIso
        ((Functor.whiskeringLeft _ _ (Type w)).obj (opOp T ⋙ Y.op))
  let e₂ : yoneda ⋙ (Functor.whiskeringLeft _ _ (Type w)).obj (opOp T ⋙ (Y ⋙ U.leftAdjoint).op) ≅
      (yoneda ⋙ (Functor.whiskeringLeft _ _ (Type w)).obj (opOp T' ⋙ Y'.op)) ⋙
        (Functor.whiskeringLeft T T' (Type w)).obj G :=
    Functor.isoWhiskerLeft yoneda ((Functor.whiskeringLeft _ _ _).mapIso
      (Functor.isoWhiskerLeft (opOp T) (NatIso.op β)))
  let e₀ : U ⋙ (cardinalContinuous T κ).ι ≅
      (cardinalContinuous T' κ).ι ⋙ (Functor.whiskeringLeft T T' (Type w)).obj G :=
    e₁ ≪≫ e₂ ≪≫ Functor.isoWhiskerRight (ιModelsIsoYoneda T' κ).symm _
  have hG : PreservesCardinalSmallLimits G κ := by
    intro J _ hJ
    refine ⟨fun {K} ↦ ⟨fun {c} hc ↦ ⟨coyonedaJointlyReflectsLimits _ _ fun t' ↦ ?_⟩⟩⟩
    have := (U.obj (Y'.obj t')).property J hJ
    have h₁ : IsLimit ((U.obj (Y'.obj t')).obj.mapCone c) := isLimitOfPreserves _ hc
    have h₂ : IsLimit ((G ⋙ shrinkCoyoneda.obj t').mapCone c) :=
      IsLimit.mapConeEquiv (e₀.app (Y'.obj t')) h₁
    exact IsLimit.mapConeEquiv (Functor.isoWhiskerLeft G (shrinkCoyonedaIsoCoyoneda.app t')) h₂
  exact ⟨G, hG, ⟨((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso e₀⟩⟩

end Converse

end LeanPool.LocallyPresentableCategories
