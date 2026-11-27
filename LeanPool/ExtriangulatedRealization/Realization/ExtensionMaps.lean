/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.Realization.ShadowHom

/-!
# The connecting maps of the realization functor

The map on extension classes comes from the shadow comparison and the bijection
on morphisms into the shifted realization. It determines how a realization triangle
maps into the derived category.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Opposite Statement IntervalLabel ZeroObject DerivedCategory

universe u

variable {k : Type u} [Field k] {I : Type u} [LinearOrder I]

attribute [local instance] HasDerivedCategory.standard

namespace RealizationData

variable {D : Iᵒᵖ ⥤ ModuleCat.{u} k} {J : Set I} (R : RealizationData D J) (hR : R.IsCompatible)

/-- The realization functor on `C_J`. -/
noncomputable abbrev realP :
    (labelsIn D J).FullSubcategory ⥤ HomotopyCategory R.Q (ComplexShape.up ℤ) :=
  (cdjEquiv J D).inverse ⋙ R.realF hR

/-- `Γ ∘ F ≅ single ∘ ρ` on `C_J`. -/
noncomputable def shadowRealPIso :
    R.realP hR ⋙ R.shadow ≅ (labelsIn D J).ι ⋙ rho D ⋙ singleFunctor (Rep k I) 0 :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (cdjEquiv J D).inverse (R.shadowRealIso hR) ≪≫
    (Functor.associator (cdjEquiv J D).inverse (cdjEquiv J D).functor
      ((labelsIn D J).ι ⋙ rho D ⋙ singleFunctor (Rep k I) 0)).symm ≪≫
    Functor.isoWhiskerRight (cdjEquiv J D).counitIso
      ((labelsIn D J).ι ⋙ rho D ⋙ singleFunctor (Rep k I) 0)
    ≪≫ Functor.leftUnitor _

lemma shadow_bijective_realP (C A : (labelsIn D J).FullSubcategory) :
    Function.Bijective (R.shadow.map :
      ((R.realP hR).obj C ⟶ ((R.realP hR).obj A)⟦(1 : ℤ)⟧) → _) :=
  R.shadow_bijective_realF hR _ _

/-! ### The maps `η` -/

attribute [local instance] HasExt.standard

/-- The extriangulated data of `C_J`. -/
noncomputable abbrev dataJ : ExtriangulatedData.{u + 1} k (labelsIn D J).FullSubcategory :=
  (cdData D).restrict (labelsIn D J)

/-- The image under `Γ` of `η δ`. -/
noncomputable def etaTarget (C A : (labelsIn D J).FullSubcategory) :
    (dataJ (D := D) (J := J)).Ext C A →+
      (R.shadow.obj ((R.realP hR).obj C) ⟶ R.shadow.obj (((R.realP hR).obj A)⟦(1 : ℤ)⟧)) :=
  (Preadditive.leftComp _ ((R.shadowRealPIso hR).app C).hom).comp
    ((Preadditive.rightComp _ ((((R.shadowRealPIso hR).app A).inv)⟦(1 : ℤ)⟧' ≫
      ((R.shadow.commShiftIso (1 : ℤ)).app _).inv)).comp
      (Abelian.Ext.homAddEquiv (X := (rho D).obj C.obj) (Y := (rho D).obj A.obj)
        (n := 1)).toAddMonoidHom)

lemma etaTarget_apply (C A : (labelsIn D J).FullSubcategory)
    (δ : (dataJ (D := D) (J := J)).Ext C A) :
    R.etaTarget hR C A δ = ((R.shadowRealPIso hR).app C).hom ≫
      (δ : Abelian.Ext.{u + 1} ((rho D).obj C.obj) ((rho D).obj A.obj) 1).hom ≫
      (((R.shadowRealPIso hR).app A).inv)⟦(1 : ℤ)⟧' ≫
        ((R.shadow.commShiftIso (1 : ℤ)).app _).inv := rfl

/-- The map `η : E(C, A) → K(Q)(F C, (F A)⟦1⟧)`. -/
noncomputable def eta (C A : (labelsIn D J).FullSubcategory) :
    (dataJ (D := D) (J := J)).Ext C A →+ ((R.realP hR).obj C ⟶ ((R.realP hR).obj A)⟦(1 : ℤ)⟧) :=
  ((AddEquiv.ofBijective R.shadow.mapAddHom
    (R.shadow_bijective_realP hR C A)).symm.toAddMonoidHom).comp
    (R.etaTarget hR C A)

lemma shadow_map_eta (C A : (labelsIn D J).FullSubcategory)
    (δ : (dataJ (D := D) (J := J)).Ext C A) :
    R.shadow.map (R.eta hR C A δ) = R.etaTarget hR C A δ :=
  (AddEquiv.ofBijective R.shadow.mapAddHom (R.shadow_bijective_realP hR C A)).apply_symm_apply _

end RealizationData

end ExtriangulatedRealization
