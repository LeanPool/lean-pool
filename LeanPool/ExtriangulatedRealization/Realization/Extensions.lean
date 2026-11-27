/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.Realization.ExtensionMaps

/-!
# Naturality and bijectivity of the connecting maps (Proposition 2.3, Step 3)

Pulling back or pushing forward an extension corresponds to composition with the
realization of the inducing morphism. The connecting maps are bijective by the
comparison with the derived category.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Opposite Statement IntervalLabel ZeroObject DerivedCategory

universe u

variable {k : Type u} [Field k] {I : Type u} [LinearOrder I]

attribute [local instance] HasDerivedCategory.standard

namespace RealizationData

variable {D : Iᵒᵖ ⥤ ModuleCat.{u} k} {J : Set I} (R : RealizationData D J) (hR : R.IsCompatible)

instance : (cdjEquiv J D).functor.Additive := inferInstanceAs (cdjLift J D).Additive

instance : (R.realF hR).Additive := by
  unfold realF
  infer_instance

attribute [local instance] HasExt.standard

omit R hR in
lemma dataJ_push {C A A' : (labelsIn D J).FullSubcategory} (a : A ⟶ A')
    (δ : (dataJ (D := D) (J := J)).Ext C A) :
    ((dataJ (D := D) (J := J)).push a δ : Abelian.Ext.{u + 1} _ _ 1) =
      (δ : Abelian.Ext.{u + 1} ((rho D).obj C.obj) ((rho D).obj A.obj) 1).comp
        (Abelian.Ext.mk₀ ((rho D).map a.hom)) (add_zero 1) := rfl

omit R hR in
lemma dataJ_pull {C'' C A : (labelsIn D J).FullSubcategory} (c : C'' ⟶ C)
    (δ : (dataJ (D := D) (J := J)).Ext C A) :
    ((dataJ (D := D) (J := J)).pull c δ : Abelian.Ext.{u + 1} _ _ 1) =
      (Abelian.Ext.mk₀ ((rho D).map c.hom)).comp
        (δ : Abelian.Ext.{u + 1} ((rho D).obj C.obj) ((rho D).obj A.obj) 1) (zero_add 1) := rfl

lemma shadow_map_shift_realP {A A' : (labelsIn D J).FullSubcategory} (a : A ⟶ A') :
    ((R.shadow.commShiftIso (1 : ℤ)).app ((R.realP hR).obj A)).inv ≫
        R.shadow.map (((R.realP hR).map a)⟦(1 : ℤ)⟧') =
      (R.shadow.map ((R.realP hR).map a))⟦(1 : ℤ)⟧' ≫
        ((R.shadow.commShiftIso (1 : ℤ)).app ((R.realP hR).obj A')).inv := by
  rw [Iso.inv_comp_eq]
  simp only [Iso.app_hom, Iso.app_inv]
  rw [← Category.assoc, ← R.shadow.commShiftIso_hom_naturality, Category.assoc,
    Iso.hom_inv_id_app]
  exact (Category.comp_id _).symm

lemma eta_push {C A A' : (labelsIn D J).FullSubcategory} (a : A ⟶ A')
    (δ : (dataJ (D := D) (J := J)).Ext C A) :
    R.eta hR C A' ((dataJ (D := D) (J := J)).push a δ) =
      R.eta hR C A δ ≫ ((R.realP hR).map a)⟦(1 : ℤ)⟧' := by
  let δ : Abelian.Ext.{u + 1} ((rho D).obj C.obj) ((rho D).obj A.obj) 1 := δ
  apply (R.shadow_bijective_realP hR C A').1
  have hΘ := (R.shadowRealPIso hR).inv.naturality a
  dsimp at hΘ
  calc R.shadow.map (R.eta hR C A' ((dataJ (D := D) (J := J)).push a δ))
      = ((R.shadowRealPIso hR).app C).hom ≫ (δ.comp (Abelian.Ext.mk₀ ((rho D).map a.hom))
          (add_zero 1)).hom ≫ (((R.shadowRealPIso hR).app A').inv)⟦(1 : ℤ)⟧' ≫
          ((R.shadow.commShiftIso (1 : ℤ)).app _).inv := R.shadow_map_eta hR C A' _
    _ = ((R.shadowRealPIso hR).app C).hom ≫ δ.hom ≫
          ((singleFunctor (Rep k I) 0).map ((rho D).map a.hom) ≫
            ((R.shadowRealPIso hR).app A').inv)⟦(1 : ℤ)⟧' ≫
          ((R.shadow.commShiftIso (1 : ℤ)).app _).inv := by
        rw [Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom, ShiftedHom.comp_mk₀, Functor.map_comp]
        simp only [Category.assoc]
        rfl
    _ = ((R.shadowRealPIso hR).app C).hom ≫ δ.hom ≫
          (((R.shadowRealPIso hR).app A).inv ≫ R.shadow.map ((R.realP hR).map a))⟦(1 : ℤ)⟧' ≫
          ((R.shadow.commShiftIso (1 : ℤ)).app _).inv := by
        rw [Iso.app_inv, Iso.app_inv, hΘ]
        rfl
    _ = (((R.shadowRealPIso hR).app C).hom ≫ δ.hom ≫
          (((R.shadowRealPIso hR).app A).inv)⟦(1 : ℤ)⟧' ≫
          ((R.shadow.commShiftIso (1 : ℤ)).app _).inv) ≫
          R.shadow.map (((R.realP hR).map a)⟦(1 : ℤ)⟧') := by
        rw [Functor.map_comp]
        simp only [Category.assoc, R.shadow_map_shift_realP hR a]
    _ = R.shadow.map (R.eta hR C A δ) ≫ R.shadow.map (((R.realP hR).map a)⟦(1 : ℤ)⟧') :=
        congrArg (· ≫ _) (R.shadow_map_eta hR C A δ).symm
    _ = R.shadow.map (R.eta hR C A δ ≫ ((R.realP hR).map a)⟦(1 : ℤ)⟧') :=
        (R.shadow.map_comp _ _).symm

lemma eta_pull {C'' C A : (labelsIn D J).FullSubcategory} (c : C'' ⟶ C)
    (δ : (dataJ (D := D) (J := J)).Ext C A) :
    R.eta hR C'' A ((dataJ (D := D) (J := J)).pull c δ) = (R.realP hR).map c ≫ R.eta hR C A δ := by
  let δ : Abelian.Ext.{u + 1} ((rho D).obj C.obj) ((rho D).obj A.obj) 1 := δ
  apply (R.shadow_bijective_realP hR C'' A).1
  have hΘ := (R.shadowRealPIso hR).hom.naturality c
  dsimp at hΘ
  calc R.shadow.map (R.eta hR C'' A ((dataJ (D := D) (J := J)).pull c δ))
      = ((R.shadowRealPIso hR).app C'').hom ≫ ((Abelian.Ext.mk₀ ((rho D).map c.hom)).comp δ
          (zero_add 1)).hom ≫ (((R.shadowRealPIso hR).app A).inv)⟦(1 : ℤ)⟧' ≫
          ((R.shadow.commShiftIso (1 : ℤ)).app _).inv := R.shadow_map_eta hR C'' A _
    _ = (((R.shadowRealPIso hR).app C'').hom ≫
          (singleFunctor (Rep k I) 0).map ((rho D).map c.hom)) ≫ δ.hom ≫
          (((R.shadowRealPIso hR).app A).inv)⟦(1 : ℤ)⟧' ≫
          ((R.shadow.commShiftIso (1 : ℤ)).app _).inv := by
        rw [Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom, ShiftedHom.mk₀_comp]
        simp only [Category.assoc]
    _ = R.shadow.map ((R.realP hR).map c) ≫ (((R.shadowRealPIso hR).app C).hom ≫ δ.hom ≫
          (((R.shadowRealPIso hR).app A).inv)⟦(1 : ℤ)⟧' ≫
          ((R.shadow.commShiftIso (1 : ℤ)).app _).inv) := by
        rw [Iso.app_hom, Iso.app_hom, ← hΘ, Category.assoc]
        rfl
    _ = R.shadow.map ((R.realP hR).map c) ≫ R.shadow.map (R.eta hR C A δ) :=
        congrArg (_ ≫ ·) (R.shadow_map_eta hR C A δ).symm
    _ = R.shadow.map ((R.realP hR).map c ≫ R.eta hR C A δ) := (R.shadow.map_comp _ _).symm

lemma etaTarget_bijective (C A : (labelsIn D J).FullSubcategory) :
    Function.Bijective (R.etaTarget hR C A) := by
  let β : ((singleFunctor (Rep k I) 0).obj ((rho D).obj A.obj))⟦(1 : ℤ)⟧ ≅
      R.shadow.obj (((R.realP hR).obj A)⟦(1 : ℤ)⟧) :=
    (shiftFunctor _ (1 : ℤ)).mapIso ((R.shadowRealPIso hR).app A).symm ≪≫
      ((R.shadow.commShiftIso (1 : ℤ)).app _).symm
  have h : ⇑(R.etaTarget hR C A) =
      (Iso.homCongr ((R.shadowRealPIso hR).app C).symm β) ∘
        (Abelian.Ext.homEquiv (X := (rho D).obj C.obj) (Y := (rho D).obj A.obj) (n := 1)) := by
    funext δ
    simp only [Iso.homCongr, β]
    rfl
  rw [h]
  exact (Iso.homCongr _ β).bijective.comp Abelian.Ext.homEquiv.bijective

lemma eta_bijective (C A : (labelsIn D J).FullSubcategory) : Function.Bijective (R.eta hR C A) :=
  (AddEquiv.ofBijective R.shadow.mapAddHom
    (R.shadow_bijective_realP hR C A)).symm.bijective.comp (R.etaTarget_bijective hR C A)

end RealizationData

end ExtriangulatedRealization
