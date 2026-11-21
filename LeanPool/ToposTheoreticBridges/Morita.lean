/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.Basic
public import Mathlib.CategoryTheory.Idempotents.FunctorCategories
public import Mathlib.CategoryTheory.Idempotents.FunctorExtension
public import Mathlib.CategoryTheory.Functor.KanExtension.DenseAtYoneda
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.ObjectProperty.Retract

/-!
# Morita equivalence and Cauchy completion

We prove that two small categories `C` and `D` are Morita equivalent (their presheaf topoi
`Cᵒᵖ ⥤ Type u` and `Dᵒᵖ ⥤ Type u` are equivalent) if and only if their idempotent completions
(Karoubi envelopes, or Cauchy completions) `Karoubi C` and `Karoubi D` are equivalent:
`moritaEquivalentCat_iff_karoubi`.

## Proof

* (`⇐`, `moritaEquivalentCat_of_karoubi`) Since `Type u` is idempotent complete, restriction
  along `toKaroubi` is an equivalence `(Karoubi Cᵒᵖ ⥤ Type u) ≌ (Cᵒᵖ ⥤ Type u)`, and
  `Karoubi Cᵒᵖ ≌ (Karoubi C)ᵒᵖ` (`karoubiOpEquiv`). An equivalence `Karoubi C ≌ Karoubi D`
  then induces an equivalence of presheaf categories.
* (`⇒`, `karoubi_of_moritaEquivalentCat`) We characterise the retracts of representable
  presheaves intrinsically: a presheaf `P` is a retract of a representable presheaf if and only
  if every morphism from `P` to the point of a small colimit cocone factors through one of the
  legs of the cocone (`FactorsThroughColimits`, `isRetractOfRepresentable_iff`). The `⇒` part
  of this uses the density of the Yoneda embedding (`Functor.denseAt`) applied to `𝟙 P`.
  This property is invariant under equivalences of categories, so an equivalence of presheaf
  categories identifies retracts of representables. Finally, for any small category `C`, the
  full subcategory of retracts of representables in `Cᵒᵖ ⥤ Type u` is equivalent to
  `Karoubi C` (`karoubiEquivOfRetract`): it is idempotent complete, and the Yoneda embedding is
  fully faithful with every object a retract of one in its image.

We do not formalise the finer statement that an equivalence of presheaf topoi is induced by an
equivalence of Cauchy completions up to natural isomorphism, nor the description of the
retracts of representables as the tiny (or indecomposable projective) objects.
-/

@[expose] public section

namespace LeanPool.ToposTheoreticBridges

open CategoryTheory Limits Idempotents Opposite

universe u u₁ v₁ u₂ v₂

/-- The category of types is idempotent complete: an idempotent `p` on `X` splits through the
subtype of fixed points of `p`. -/
instance isIdempotentComplete_type : IsIdempotentComplete (Type u) where
  idempotents_split X p hp := by
    refine ⟨{ x : X // p x = x }, TypeCat.ofHom Subtype.val,
      TypeCat.ofHom fun x => ⟨p x, ?_⟩, ?_, ?_⟩
    · exact congr($hp x)
    · ext x; exact x.2
    · rfl

section General

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]

/-- A full subcategory, stable under retracts, of an idempotent complete category is
idempotent complete. -/
theorem isIdempotentComplete_fullSubcategory [IsIdempotentComplete B] (P : ObjectProperty B)
    [P.IsStableUnderRetracts] : IsIdempotentComplete P.FullSubcategory where
  idempotents_split X p hp := by
    obtain ⟨Y, i, e, h₁, h₂⟩ := IsIdempotentComplete.idempotents_split X.obj p.hom
      (by rw [← ObjectProperty.FullSubcategory.comp_hom, hp])
    exact ⟨⟨Y, P.prop_of_retract ⟨i, e, h₁⟩ X.2⟩, ObjectProperty.homMk i,
      ObjectProperty.homMk e, by ext; exact h₁, by ext; exact h₂⟩

/-- A retract between the underlying objects of two objects of a full subcategory is a
retract in the full subcategory. -/
def retractFullSubcategoryMk {P : ObjectProperty B} {X Y : P.FullSubcategory}
    (r : Retract X.obj Y.obj) : Retract X Y where
  i := ObjectProperty.homMk r.i
  r := ObjectProperty.homMk r.r
  retract := by ext; exact r.retract

/-- A fully faithful functor out of an idempotent complete category, such that every object
of the target is a retract of an object of the image, is essentially surjective. -/
theorem essSurj_of_forall_retract [IsIdempotentComplete A] (G : A ⥤ B) [G.Full] [G.Faithful]
    (h : ∀ b : B, ∃ a : A, Nonempty (Retract b (G.obj a))) : G.EssSurj where
  mem_essImage b := by
    obtain ⟨a, ⟨r⟩⟩ := h b
    obtain ⟨Y, i, e, h₁, h₂⟩ := IsIdempotentComplete.idempotents_split a
      (G.preimage (r.r ≫ r.i)) (G.map_injective (by simp))
    have h₃ : G.map e ≫ G.map i = r.r ≫ r.i := by rw [← G.map_comp, h₂, G.map_preimage]
    refine ⟨Y, ⟨⟨G.map i ≫ r.r, r.i ≫ G.map e, ?_, ?_⟩⟩⟩
    · calc _ = G.map i ≫ (r.r ≫ r.i) ≫ G.map e := by simp
        _ = 𝟙 _ := by simp only [← h₃, ← G.map_comp, Category.assoc, reassoc_of% h₁, h₁,
          G.map_id]
    · calc _ = r.i ≫ (G.map e ≫ G.map i) ≫ r.r := by simp
        _ = 𝟙 _ := by simp [h₃]

/-- The extension to idempotent completions of a faithful functor is faithful. -/
instance faithful_functorExtension₂_obj (F : A ⥤ B) [F.Faithful] :
    ((functorExtension₂ A B).obj F).Faithful where
  map_injective {P Q} f g hfg := by
    ext
    exact F.map_injective (congr_arg Karoubi.Hom.f hfg)

/-- The extension to idempotent completions of a fully faithful functor is full. -/
instance full_functorExtension₂_obj (F : A ⥤ B) [F.Full] [F.Faithful] :
    ((functorExtension₂ A B).obj F).Full where
  map_surjective {P Q} φ := by
    obtain ⟨f, hf⟩ := F.map_surjective (X := P.X) (Y := Q.X) φ.f
    refine ⟨⟨f, F.map_injective ?_⟩, ?_⟩
    · simp only [Functor.map_comp, hf]
      exact φ.comm
    · ext; exact hf

/-- If `F : A ⥤ B` is fully faithful, `B` is idempotent complete and every object of `B` is a
retract of an object in the image of `F`, then `B` is equivalent to the idempotent completion
of `A`. -/
noncomputable def karoubiEquivOfRetract [IsIdempotentComplete B] (F : A ⥤ B) [F.Full]
    [F.Faithful] (h : ∀ b : B, ∃ a : A, Nonempty (Retract b (F.obj a))) : Karoubi A ≌ B :=
  have : ((functorExtension₂ A B).obj F).EssSurj := essSurj_of_forall_retract _ fun Q => by
    obtain ⟨a, ⟨r⟩⟩ := h Q.X
    exact ⟨(toKaroubi A).obj a, ⟨(Karoubi.retract Q).trans ((r.map (toKaroubi B)).trans
      (Retract.ofIso ((((functorExtension₂CompWhiskeringLeftToKaroubiIso A B).app F).app
        a).symm)))⟩⟩
  have : ((functorExtension₂ A B).obj F).IsEquivalence := { }
  ((functorExtension₂ A B).obj F).asEquivalence.trans (toKaroubiEquivalence B).symm

/-- The idempotent completion of the opposite category is the opposite of the idempotent
completion. -/
noncomputable def karoubiOpEquiv (A : Type u₁) [Category.{v₁} A] :
    Karoubi Aᵒᵖ ≌ (Karoubi A)ᵒᵖ :=
  karoubiEquivOfRetract (toKaroubi A).op fun b => ⟨op b.unop.X, ⟨(Karoubi.retract b.unop).op⟩⟩

/-- An object `P` *factors through colimits* when every morphism from `P` to the point of a
colimit cocone indexed by a `u`-small category factors through one of the legs of the cocone.
This holds for instance when `Hom(P, -)` preserves `u`-small colimits. -/
def FactorsThroughColimits {E : Type u₁} [Category.{v₁} E] (P : E) : Prop :=
  ∀ (J : Type u) [SmallCategory J] (G : J ⥤ E) (c : Cocone G), IsColimit c →
    ∀ f : P ⟶ c.pt, ∃ (j : J) (g : P ⟶ G.obj j), f = g ≫ c.ι.app j

/-- A retract of an object which factors through colimits factors through colimits. -/
theorem FactorsThroughColimits.of_retract {E : Type u₁} [Category.{v₁} E] {P Q : E}
    (r : Retract P Q) (hQ : FactorsThroughColimits.{u} Q) : FactorsThroughColimits.{u} P := by
  intro J _ G c hc f
  obtain ⟨j, g, hg⟩ := hQ J G c hc (r.r ≫ f)
  exact ⟨j, r.i ≫ g, by rw [Category.assoc, ← hg, r.retract_assoc]⟩

/-- Factoring through colimits is invariant under equivalences of categories. -/
theorem FactorsThroughColimits.of_equivalence {E : Type u₁} [Category.{v₁} E] {E' : Type u₂}
    [Category.{v₂} E'] (e : E ≌ E') {P : E} (hP : FactorsThroughColimits.{u} P) :
    FactorsThroughColimits.{u} (e.functor.obj P) := by
  intro J _ G c hc f
  obtain ⟨j, g, hg⟩ := hP J (G ⋙ e.inverse) (e.inverse.mapCocone c)
    (isColimitOfPreserves e.inverse hc) (e.toAdjunction.homEquiv _ _ f)
  refine ⟨j, (e.toAdjunction.homEquiv _ _).symm g, ?_⟩
  rw [← Adjunction.homEquiv_naturality_right_symm]
  exact (((e.toAdjunction.homEquiv _ _).symm_apply_eq).2 hg.symm).symm

end General

section Presheaf

variable (C : Type u) [SmallCategory C]

/-- The property of a presheaf of being a retract of a representable presheaf. -/
def isRetractOfRepresentable : ObjectProperty (Cᵒᵖ ⥤ Type u) :=
  fun P => ∃ X : C, Nonempty (Retract P (yoneda.obj X))

/-- Retracts of representable presheaves are stable under retracts. -/
instance : (isRetractOfRepresentable C).IsStableUnderRetracts where
  of_retract r := fun ⟨X, ⟨r'⟩⟩ => ⟨X, ⟨r.trans r'⟩⟩

/-- The full subcategory of retracts of representable presheaves is idempotent complete. -/
instance : IsIdempotentComplete (isRetractOfRepresentable C).FullSubcategory :=
  isIdempotentComplete_fullSubcategory _

variable {C}

/-- Representable presheaves factor through colimits. -/
theorem factorsThroughColimits_yoneda (X : C) :
    FactorsThroughColimits.{u} (yoneda.obj X) := by
  intro J _ G c hc f
  obtain ⟨j, x, hx⟩ := Types.jointly_surjective _
    (isColimitOfPreserves ((evaluation Cᵒᵖ (Type u)).obj (op X)) hc) (yonedaEquiv f)
  refine ⟨j, yonedaEquiv.symm x, yonedaEquiv.injective ?_⟩
  rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
  exact hx.symm

/-- A presheaf is a retract of a representable presheaf if and only if it factors through
colimits. The converse direction applies the factorisation property to the identity of `P`,
written as a colimit of representable presheaves. -/
theorem isRetractOfRepresentable_iff (P : Cᵒᵖ ⥤ Type u) :
    isRetractOfRepresentable C P ↔ FactorsThroughColimits.{u} P := by
  constructor
  · rintro ⟨X, ⟨r⟩⟩
    exact (factorsThroughColimits_yoneda X).of_retract r
  · intro hP
    obtain ⟨j, g, hg⟩ := hP _ _ _ (yoneda.denseAt P) (𝟙 P)
    exact ⟨j.left, ⟨⟨g, _, hg.symm⟩⟩⟩

/-- An equivalence of presheaf categories preserves retracts of representable presheaves. -/
theorem isRetractOfRepresentable_functor_obj {D : Type u} [SmallCategory D]
    (e : (Cᵒᵖ ⥤ Type u) ≌ (Dᵒᵖ ⥤ Type u)) {P : Cᵒᵖ ⥤ Type u}
    (hP : isRetractOfRepresentable C P) : isRetractOfRepresentable D (e.functor.obj P) := by
  rw [isRetractOfRepresentable_iff] at hP ⊢
  exact hP.of_equivalence e

variable (C)

/-- The idempotent completion of a small category `C` is equivalent to the full subcategory of
retracts of representable presheaves on `C`. -/
noncomputable def karoubiEquivRetractsOfRepresentables :
    Karoubi C ≌ (isRetractOfRepresentable C).FullSubcategory :=
  karoubiEquivOfRetract ((isRetractOfRepresentable C).lift yoneda
      (fun X => ⟨X, ⟨Retract.refl (yoneda.obj X)⟩⟩ : ∀ X : C, _)) fun Q => by
    obtain ⟨X, ⟨r⟩⟩ := Q.2
    exact ⟨X, ⟨retractFullSubcategoryMk r⟩⟩

end Presheaf

/-- If two small categories are Morita equivalent, their idempotent completions are
equivalent. -/
theorem karoubi_of_moritaEquivalentCat {C D : Type u} [SmallCategory C] [SmallCategory D]
    (h : MoritaEquivalentCat C D) : Nonempty (Karoubi C ≌ Karoubi D) := by
  obtain ⟨e⟩ := h
  refine ⟨(karoubiEquivOfRetract ((isRetractOfRepresentable D).lift (yoneda ⋙ e.functor)
    fun X => isRetractOfRepresentable_functor_obj e ⟨X, ⟨Retract.refl _⟩⟩) fun Q => ?_).trans
    (karoubiEquivRetractsOfRepresentables D).symm⟩
  obtain ⟨X, ⟨r⟩⟩ := isRetractOfRepresentable_functor_obj e.symm Q.2
  exact ⟨X, ⟨retractFullSubcategoryMk
    ((Retract.ofIso (e.counitIso.app Q.obj).symm).trans (r.map e.functor))⟩⟩

/-- If the idempotent completions of two small categories are equivalent, the categories are
Morita equivalent. -/
theorem moritaEquivalentCat_of_karoubi {C D : Type u} [SmallCategory C] [SmallCategory D]
    (e : Karoubi C ≌ Karoubi D) : MoritaEquivalentCat C D :=
  ⟨(karoubiUniversal Cᵒᵖ (Type u)).trans <| (karoubiOpEquiv C).congrLeft.trans <|
    e.op.congrLeft.trans <| (karoubiOpEquiv D).congrLeft.symm.trans
      (karoubiUniversal Dᵒᵖ (Type u)).symm⟩

/-- Two small categories are Morita equivalent if and only if their idempotent completions
(Cauchy completions) are equivalent. -/
theorem moritaEquivalentCat_iff_karoubi (C D : Type u) [SmallCategory C] [SmallCategory D] :
    MoritaEquivalentCat C D ↔ Nonempty (Karoubi C ≌ Karoubi D) :=
  ⟨karoubi_of_moritaEquivalentCat, fun ⟨e⟩ => moritaEquivalentCat_of_karoubi e⟩

end LeanPool.ToposTheoreticBridges
