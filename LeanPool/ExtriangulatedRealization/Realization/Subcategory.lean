/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.Realization.Extriangulated
public import LeanPool.ExtriangulatedRealization.Categories.Biproduct

/-!
# The subcategories `C_J` are extriangulated (Proposition 2.3, Corollary 2.4)

The induced structure on `C_J` consists of the restricted extension bifunctor and realizations,
and the binary biproducts of `C(D)`, which `C_J` contains. The axioms not involving biproducts
pass from `C(D)` to `C_J` because `C_J` is full and closed under extensions: the new middle terms
in the existence axiom and in (ET4), (ET4)ᵒᵖ lie in `C_J`. A biproduct chosen in `C_J` is only
isomorphic to the one of `C(D)`; for (ET2) we transport realizations of `C(D)` along
isomorphisms of their end terms, which holds since every finite diagram lies in some
`C_{Iic m}`, where realizations are the sequences going to distinguished triangles.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Opposite Statement IntervalLabel Abelian

universe u

attribute [local instance] HasExt.standard

variable {k : Type u} [Field k] {I : Type u} [LinearOrder I] (D : Iᵒᵖ ⥤ ModuleCat.{u} k)

/-! ### Functoriality of `E` -/

lemma cdData_push_comp {C A A' A'' : CD D} (a : A ⟶ A') (a' : A' ⟶ A'')
    (δ : (cdData D).Ext C A) :
    (cdData D).push a' ((cdData D).push a δ) = (cdData D).push (a ≫ a') δ := by
  change ((δ : Ext.{u + 1} ((rho D).obj C) ((rho D).obj A) 1).comp
      (Ext.mk₀ ((rho D).map a)) (add_zero 1)).comp (Ext.mk₀ ((rho D).map a')) (add_zero 1) =
    (δ : Ext.{u + 1} ((rho D).obj C) ((rho D).obj A) 1).comp
      (Ext.mk₀ ((rho D).map (a ≫ a'))) (add_zero 1)
  rw [Functor.map_comp, ← Ext.mk₀_comp_mk₀]
  exact Ext.comp_assoc_of_third_deg_zero _ _ _ _

lemma cdData_pull_push {C'' C A A' : CD D} (c : C'' ⟶ C) (a : A ⟶ A')
    (δ : (cdData D).Ext C A) :
    (cdData D).pull c ((cdData D).push a δ) = (cdData D).push a ((cdData D).pull c δ) := by
  change (Ext.mk₀ ((rho D).map c)).comp ((δ : Ext.{u + 1} ((rho D).obj C) ((rho D).obj A) 1).comp
      (Ext.mk₀ ((rho D).map a)) (add_zero 1)) (zero_add 1) =
    ((Ext.mk₀ ((rho D).map c)).comp (δ : Ext.{u + 1} ((rho D).obj C) ((rho D).obj A) 1)
      (zero_add 1)).comp (Ext.mk₀ ((rho D).map a)) (add_zero 1)
  exact (Ext.comp_assoc_of_third_deg_zero _ _ _ _).symm

variable [WellFoundedLT I] [Nonempty I]

/-- Realizations in `C(D)` are invariant under isomorphisms of the end terms. -/
lemma cd_realizes_transport (hD : HasSurjectiveTransitions D) {A' A B C C' : CD D}
    {δ : (cdData D).Ext C A} {x : A ⟶ B} {y : B ⟶ C} (h : (cdData D).Realizes δ x y)
    (a : A' ≅ A) (c : C' ≅ C) :
    (cdData D).Realizes ((cdData D).pull c.hom ((cdData D).push a.inv δ)) (a.hom ≫ x)
      (y ≫ c.inv) := by
  obtain ⟨m, hm⟩ := exists_labelsIn_Iic D [A', A, B, C, C']
  exact (iicData D m).realizes_transport (iicData_isCompatible D hD m)
    (A := ⟨A, hm A (by simp)⟩) (B := ⟨B, hm B (by simp)⟩) (C := ⟨C, hm C (by simp)⟩)
    (A' := ⟨A', hm A' (by simp)⟩) (C' := ⟨C', hm C' (by simp)⟩)
    (x := ObjectProperty.homMk x) (y := ObjectProperty.homMk y) h
    (ObjectProperty.isoMk _ a) (ObjectProperty.isoMk _ c)

/-! ### Biproducts of a full subcategory closed under biproducts -/

section Biproducts

variable {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] [HasBinaryBiproducts 𝒞] {P : ObjectProperty 𝒞}
  [HasBinaryBiproducts P.FullSubcategory]

/-- The biproduct chosen in a full subcategory, compared with the one of the ambient
category. -/
noncomputable def biprodObjIso (X Y : P.FullSubcategory) : (X ⊞ Y).obj ≅ X.obj ⊞ Y.obj :=
  isoBiprodOfTotal (biprod.inl : X ⟶ X ⊞ Y).hom (biprod.inr : Y ⟶ X ⊞ Y).hom
    (biprod.fst : X ⊞ Y ⟶ X).hom (biprod.snd : X ⊞ Y ⟶ Y).hom
    (congrArg InducedCategory.Hom.hom (biprod.inl_fst (X := X) (Y := Y)))
    (congrArg InducedCategory.Hom.hom (biprod.inr_snd (X := X) (Y := Y)))
    (congrArg InducedCategory.Hom.hom (biprod.inl_snd (X := X) (Y := Y)))
    (congrArg InducedCategory.Hom.hom (biprod.inr_fst (X := X) (Y := Y)))
    (congrArg InducedCategory.Hom.hom (biprod.total (X := X) (Y := Y)))

lemma inl_biprodObjIso_inv (X Y : P.FullSubcategory) :
    biprod.inl ≫ (biprodObjIso X Y).inv = (biprod.inl : X ⟶ X ⊞ Y).hom := by
  simp [biprodObjIso]

lemma inr_biprodObjIso_inv (X Y : P.FullSubcategory) :
    biprod.inr ≫ (biprodObjIso X Y).inv = (biprod.inr : Y ⟶ X ⊞ Y).hom := by
  simp [biprodObjIso]

lemma biprodObjIso_hom_fst (X Y : P.FullSubcategory) :
    (biprodObjIso X Y).hom ≫ biprod.fst = (biprod.fst : X ⊞ Y ⟶ X).hom := by
  simp [biprodObjIso]

lemma biprodObjIso_hom_snd (X Y : P.FullSubcategory) :
    (biprodObjIso X Y).hom ≫ biprod.snd = (biprod.snd : X ⊞ Y ⟶ Y).hom := by
  simp [biprodObjIso]

lemma biprod_map_hom {X Y X' Y' : P.FullSubcategory} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (biprod.map f g).hom =
      (biprodObjIso X X').hom ≫ biprod.map f.hom g.hom ≫ (biprodObjIso Y Y').inv := by
  rw [biprod.map_eq, biprod.map_eq]
  simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
    reassoc_of% biprodObjIso_hom_fst, reassoc_of% biprodObjIso_hom_snd,
    inl_biprodObjIso_inv, inr_biprodObjIso_inv]
  rfl

end Biproducts

/-! ### The axioms on `C_J` -/

omit [WellFoundedLT I] [Nonempty I] in
lemma subcatJ_biprod {J : Set I} {A B : CD D} (hA : subcatJ D J A) (hB : subcatJ D J B) :
    subcatJ D J (A ⊞ B) := by
  rw [subcatJ_eq_labelsIn] at hA hB ⊢
  exact labelsIn_biprod D hA hB

/-- **Proposition 2.3, Corollary 2.4**: each `C_J`, with the induced structure, is
extriangulated. -/
theorem subcatJ_isExtriangulatedSubcategory (hD : HasSurjectiveTransitions D) (J : Set I) :
    (cdData D).IsExtriangulatedSubcategory (subcatJ D J) := by
  refine ⟨fun A B hA hB => subcatJ_biprod D hA hB, ?_⟩
  let := ExtriangulatedData.hasBinaryBiproductsOfClosed (subcatJ D J)
    (fun A B hA hB => subcatJ_biprod D hA hB)
  have h𝔼 := cdData_isExtriangulated D hD
  have hext : (cdData D).IsExtensionClosed (subcatJ D J) := subcatJ_isExtensionClosed D J
  have hsum : ∀ {A C A' C' : (subcatJ D J).FullSubcategory} (δ : (cdData D).Ext C.obj A.obj)
      (δ' : (cdData D).Ext C'.obj A'.obj),
      ((cdData D).restrict (subcatJ D J)).sum (C₁ := C) (A₁ := A) (C₂ := C') (A₂ := A') δ δ' =
        (cdData D).pull (biprodObjIso C C').hom
          ((cdData D).push (biprodObjIso A A').inv ((cdData D).sum δ δ')) := by
    intro A C A' C' δ δ'
    change (cdData D).pull (biprod.fst : C ⊞ C' ⟶ C).hom
        ((cdData D).push (biprod.inl : A ⟶ A ⊞ A').hom δ) +
      (cdData D).pull (biprod.snd : C ⊞ C' ⟶ C').hom
        ((cdData D).push (biprod.inr : A' ⟶ A ⊞ A').hom δ') = _
    rw [ExtriangulatedData.sum, map_add, map_add, ← cdData_pull_push, ← cdData_pull_push,
      cdData_push_comp, cdData_push_comp, cdData_pull_comp, cdData_pull_comp,
      inl_biprodObjIso_inv, inr_biprodObjIso_inv, biprodObjIso_hom_fst, biprodObjIso_hom_snd]
  exact
  { push_add := fun a a' δ => h𝔼.push_add a.hom a'.hom δ
    push_smul := fun r a δ => h𝔼.push_smul r a.hom δ
    pull_add := fun c c' δ => h𝔼.pull_add c.hom c'.hom δ
    pull_smul := fun r c δ => h𝔼.pull_smul r c.hom δ
    exists_realizes := fun {C' A} δ => by
      obtain ⟨B, x, y, h⟩ := h𝔼.exists_realizes (C' := C'.obj) (A := A.obj) δ
      exact ⟨⟨B, hext h A.property C'.property⟩, ObjectProperty.homMk x,
        ObjectProperty.homMk y, h⟩
    realizes_unique := fun h h' => by
      obtain ⟨b, h₁, h₂⟩ := h𝔼.realizes_unique h h'
      exact ⟨ObjectProperty.isoMk _ b, ObjectProperty.hom_ext _ h₁, ObjectProperty.hom_ext _ h₂⟩
    realizes_iso := fun b h => h𝔼.realizes_iso ((subcatJ D J).ι.mapIso b) h
    realizes_morphism := fun h h' a c hac => by
      obtain ⟨b, h₁, h₂⟩ := h𝔼.realizes_morphism h h' a.hom c.hom hac
      exact ⟨ObjectProperty.homMk b, ObjectProperty.hom_ext _ h₁, ObjectProperty.hom_ext _ h₂⟩
    realizes_zero := fun A C' => by
      have h := h𝔼.realizes_iso (biprodObjIso A C').symm (h𝔼.realizes_zero A.obj C'.obj)
      rw [Iso.symm_hom, Iso.symm_inv, inl_biprodObjIso_inv, biprodObjIso_hom_snd] at h
      exact h
    realizes_sum := fun {A B C A' B' C' δ δ' x y x' y'} h h' => by
      have h₀ := h𝔼.realizes_iso (biprodObjIso B B').symm
        (cd_realizes_transport D hD (h𝔼.realizes_sum h h') (biprodObjIso A A')
          (biprodObjIso C C'))
      change (cdData D).Realizes _ (biprod.map x x').hom (biprod.map y y').hom
      rw [biprod_map_hom, biprod_map_hom]
      simp only [Iso.symm_hom, Iso.symm_inv, Category.assoc] at h₀
      convert h₀ using 2
      rw [hsum δ δ']
      rfl
    et3 := fun h h' a b hab => by
      obtain ⟨c, h₁, h₂⟩ := h𝔼.et3 h h' a.hom b.hom (congrArg InducedCategory.Hom.hom hab)
      exact ⟨ObjectProperty.homMk c, ObjectProperty.hom_ext _ h₁, h₂⟩
    et3_op := fun h h' b c hbc => by
      obtain ⟨a, h₁, h₂⟩ := h𝔼.et3_op h h' b.hom c.hom (congrArg InducedCategory.Hom.hom hbc)
      exact ⟨ObjectProperty.homMk a, ObjectProperty.hom_ext _ h₁, h₂⟩
    et4 := fun {A B C' D' F f f' g g' δ δ'} h h' => by
      obtain ⟨E, h'', d, e, δ'', h₁, h₂, h₃, h₄, h₅, h₆⟩ := h𝔼.et4 h h'
      exact ⟨⟨E, hext h₄ D'.property F.property⟩, ObjectProperty.homMk h'',
        ObjectProperty.homMk d, ObjectProperty.homMk e, δ'', h₁, ObjectProperty.hom_ext _ h₂,
        ObjectProperty.hom_ext _ h₃, h₄, h₅, h₆⟩
    et4_op := fun {D' A B F C' f' f g' g δ δ'} h h' => by
      obtain ⟨E, h'', d, e, δ'', h₁, h₂, h₃, h₄, h₅, h₆⟩ := h𝔼.et4_op h h'
      exact ⟨⟨E, hext h₄ D'.property F.property⟩, ObjectProperty.homMk h'',
        ObjectProperty.homMk d, ObjectProperty.homMk e, δ'', h₁, ObjectProperty.hom_ext _ h₂,
        ObjectProperty.hom_ext _ h₃, h₄, h₅, h₆⟩ }

/-- **Proposition 2.3.** -/
theorem proposition_2_3 : Proposition23.{u} := by
  intro k _ I _ _ _ D hD J W q hsurj hcomm
  exact ⟨subcatJ_isExtriangulatedSubcategory D hD J,
    hasAlgebraicRealization_subcatJ D J W q hsurj hcomm⟩

/-- **Corollary 2.4.** -/
theorem corollary_2_4 : Corollary24.{u} := by
  intro k _ I _ _ _ D hD
  refine ⟨cdData_isExtriangulated D hD, essentiallySmall_CD D,
    fun J => ⟨inferInstance, subcatJ_isExtensionClosed D J,
      subcatJ_isExtriangulatedSubcategory D hD J, ?_⟩⟩
  rintro ⟨m, -, hm⟩
  exact hasAlgebraicRealization_subcatJ D J (D.obj (op m))
    (fun i hi => D.map (homOfLE (hm i hi)).op) (fun i hi => hD (hm i hi))
    (fun i j hi hj h => by rw [← D.map_comp]; rfl)

end ExtriangulatedRealization
