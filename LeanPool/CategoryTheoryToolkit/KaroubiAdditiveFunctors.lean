/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.CategoryTheory.Idempotents.FunctorExtension
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Additive functors on the Karoubi envelope

For preadditive categories `C` and `D`, a functor `F : Karoubi C ⥤ D` is additive as soon as its
restriction `toKaroubi C ⋙ F` is. When `D` is idempotent complete, precomposition with
`toKaroubi C` is therefore an equivalence between additive functors `Karoubi C ⥤ D` and
additive functors `C ⥤ D`: the universal property of the Karoubi envelope holds in the
category of additive functors.

## Main statements

* `CategoryTheory.Idempotents.additive_iff_toKaroubi_comp`: `F` is additive iff
  `toKaroubi C ⋙ F` is;
* `CategoryTheory.Idempotents.whiskeringLeftToKaroubiAdditiveFullyFaithful`: precomposition
  with `toKaroubi C` on additive functors is fully faithful;
* `CategoryTheory.Idempotents.karoubiUniversalAdditive`: the equivalence
  `C ⥤+ D ≌ Karoubi C ⥤+ D` for `D` idempotent complete.
-/

@[expose] public section

namespace CategoryTheory
namespace Idempotents

open Category Karoubi CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D]

/-- Every morphism of `Karoubi C` factors through the image under `toKaroubi C` of its
underlying morphism. -/
theorem Karoubi.hom_eq_decompId_i_comp {P Q : Karoubi C} (f : P ⟶ Q) :
    f = P.decompId_i ≫ (toKaroubi C).map f.f ≫ Q.decompId_p := by
  ext
  simp

section Additive

variable [Preadditive C] [Preadditive D]

theorem additive_of_toKaroubi_comp (F : Karoubi C ⥤ D) [(toKaroubi C ⋙ F).Additive] :
    F.Additive where
  map_add {P Q f g} := by
    have key (h : P ⟶ Q) : F.map h =
        F.map P.decompId_i ≫ (toKaroubi C ⋙ F).map h.f ≫ F.map Q.decompId_p := by
      simpa using congr(F.map $(Karoubi.hom_eq_decompId_i_comp h))
    rw [key, key f, key g, show (f + g).f = f.f + g.f from rfl, Functor.map_add,
      Preadditive.add_comp, Preadditive.comp_add]

theorem additive_iff_toKaroubi_comp (F : Karoubi C ⥤ D) :
    F.Additive ↔ (toKaroubi C ⋙ F).Additive :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ additive_of_toKaroubi_comp F⟩

variable (C D) in
/-- The precomposition with `toKaroubi C`, as a functor between categories of additive
functors. -/
def whiskeringLeftToKaroubiAdditive : (Karoubi C ⥤+ D) ⥤ (C ⥤+ D) :=
  (additiveFunctor C D).lift
    (AdditiveFunctor.forget _ _ ⋙ (Functor.whiskeringLeft C (Karoubi C) D).obj (toKaroubi C))
    (fun F ↦ inferInstanceAs (toKaroubi C ⋙ F.obj).Additive)

/-- The precomposition with `toKaroubi C` on additive functors is fully faithful. -/
def whiskeringLeftToKaroubiAdditiveFullyFaithful :
    (whiskeringLeftToKaroubiAdditive C D).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful (G := AdditiveFunctor.forget _ _)
    ((ObjectProperty.fullyFaithfulι _).comp whiskeringLeftObjToKaroubiFullyFaithful)

instance : (whiskeringLeftToKaroubiAdditive C D).Full :=
  whiskeringLeftToKaroubiAdditiveFullyFaithful.full

instance : (whiskeringLeftToKaroubiAdditive C D).Faithful :=
  whiskeringLeftToKaroubiAdditiveFullyFaithful.faithful

variable [IsIdempotentComplete D]

instance : (whiskeringLeftToKaroubiAdditive C D).EssSurj where
  mem_essImage G := by
    let W := (Functor.whiskeringLeft C (Karoubi C) D).obj (toKaroubi C)
    let e : W.obj (W.objPreimage G.obj) ≅ G.obj := W.objObjPreimageIso G.obj
    have : (toKaroubi C ⋙ W.objPreimage G.obj).Additive := Functor.additive_of_iso e.symm
    exact ⟨⟨_, additive_of_toKaroubi_comp (W.objPreimage G.obj)⟩, ⟨ObjectProperty.isoMk _ e⟩⟩

instance : (whiskeringLeftToKaroubiAdditive C D).IsEquivalence where

variable (C D) in
/-- When `D` is idempotent complete, additive functors `C ⥤ D` are equivalent to additive
functors `Karoubi C ⥤ D`. -/
noncomputable def karoubiUniversalAdditive : C ⥤+ D ≌ Karoubi C ⥤+ D :=
  (whiskeringLeftToKaroubiAdditive C D).asEquivalence.symm

end Additive

end Idempotents
end CategoryTheory
