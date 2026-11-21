/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.CategoryTheory.ConnectedComponents
public import Mathlib.CategoryTheory.Groupoid.FreeGroupoidOfCategory
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Group.End
import Mathlib.CategoryTheory.Groupoid.Discrete
import Mathlib.CategoryTheory.Monoidal.Mon

/-!
# The fundamental groupoid of a category and the classes `W₀`, `W₁`

The fundamental groupoid of a category `A` is Mathlib's free groupoid `Π₁ A := FreeGroupoid A`,
the localization of `A` at all its morphisms (Gabriel–Zisman, *Calculus of fractions*, I.1.1).
We prove:

* `isEquivalence_freeGroupoidLift_id`: for a groupoid `G`, `Π₁ G ⥤ G` extending the identity
  is an equivalence (it is inverse to `FreeGroupoid.of G`);
* `bijective_mapConnectedComponents_freeGroupoidOf`: `π₀ (Π₁ A) = π₀ A`;
* `Groupoid.isEquivalence_iff_bijective`: a functor between groupoids is an equivalence iff it
  is bijective on connected components and on all automorphism groups;
* for the classes `W₀` (functors bijective on `π₀`) and `W₁` (functors inducing an equivalence
  of fundamental groupoids) of functors between small categories: `W₁_iff`,
  `W₁_iff_isEquivalence` and `W₁_le_W₀`.

This is Layers 1.1 and 1.2 of the roadmap *Homotopy theory of small categories*.
-/

@[expose] public section

universe v u v' u'

namespace LeanPool.HomotopyTheoryOfCategories

open CategoryTheory

section Groupoid

/-- In a groupoid, objects related by a zigzag are related by a morphism. -/
lemma Groupoid.nonempty_hom_of_zigzag {G : Type u} [Groupoid.{v} G] {a b : G}
    (h : Zigzag a b) : Nonempty (a ⟶ b) := by
  induction h with
  | refl => exact ⟨𝟙 a⟩
  | tail _ hz ih =>
    obtain ⟨f⟩ := ih
    rcases hz with ⟨⟨g⟩⟩ | ⟨⟨g⟩⟩
    · exact ⟨f ≫ g⟩
    · exact ⟨f ≫ Groupoid.inv g⟩

/-- In a groupoid, two objects lie in the same connected component iff there is a morphism
between them. -/
lemma Groupoid.mk_eq_mk_iff {G : Type u} [Groupoid.{v} G] (a b : G) :
    (Quotient.mk'' a : ConnectedComponents G) = Quotient.mk'' b ↔ Nonempty (a ⟶ b) :=
  ⟨fun h ↦ Groupoid.nonempty_hom_of_zigzag (Quotient.exact' h),
    fun ⟨f⟩ ↦ Quotient.sound' (Zigzag.of_hom f)⟩

/-- Two automorphisms are equal if their underlying morphisms are. -/
lemma Aut.ext' {C : Type u} [Category.{v} C] {X : C} {e e' : Aut X}
    (h : e.asIso.hom = e'.asIso.hom) : e = e' :=
  Aut.isoEquiv.injective (Iso.ext h)

variable {G : Type u} [Groupoid.{v} G] {H : Type u'} [Groupoid.{v'} H]

/-- A functor between groupoids is an equivalence iff it is bijective on connected components
and on the automorphism group of every object. -/
theorem Groupoid.isEquivalence_iff_bijective (Φ : G ⥤ H) :
    Φ.IsEquivalence ↔
      Function.Bijective Φ.mapConnectedComponents ∧ ∀ a : G, Function.Bijective (Φ.mapAut a) := by
  constructor
  · intro hΦ
    refine ⟨⟨?_, ?_⟩, fun a ↦ ⟨?_, ?_⟩⟩
    · rintro ⟨a⟩ ⟨b⟩ h
      obtain ⟨f⟩ := (Groupoid.mk_eq_mk_iff _ _).1 h
      exact (Groupoid.mk_eq_mk_iff a b).2 ⟨Φ.preimage f⟩
    · rintro ⟨h⟩
      exact ⟨Quotient.mk'' (Φ.objPreimage h),
        (Groupoid.mk_eq_mk_iff _ _).2 ⟨(Φ.objObjPreimageIso h).hom⟩⟩
    · intro e e' hee'
      apply Aut.ext'
      exact Φ.map_injective (congrArg (fun σ : Aut (Φ.obj a) ↦ σ.asIso.hom) hee')
    · intro σ
      refine ⟨.of (Φ.preimageIso σ.asIso), Aut.ext' ?_⟩
      simp
  · rintro ⟨h0, h1⟩
    have faithful : Φ.Faithful := ⟨fun {a b} f g hfg ↦ by
      have : Φ.mapAut a (.of (asIso (f ≫ Groupoid.inv g))) = 1 :=
        Aut.ext' (by simp [hfg])
      have h := congrArg (fun σ : Aut a ↦ σ.asIso.hom)
        ((h1 a).1 (this.trans (Φ.mapAut a).map_one.symm))
      simp only [asIso_hom, Aut.one_asIso, Iso.refl_hom] at h
      rw [← Category.comp_id f, ← Groupoid.inv_comp g, ← Category.assoc, h, Category.id_comp]⟩
    have full : Φ.Full := ⟨fun {a b} k ↦ by
      obtain ⟨m⟩ := (Groupoid.mk_eq_mk_iff a b).1 (h0.1 ((Groupoid.mk_eq_mk_iff _ _).2 ⟨k⟩))
      obtain ⟨σ, hσ⟩ := (h1 a).2 (.of (asIso (k ≫ Groupoid.inv (Φ.map m))))
      refine ⟨σ.asIso.hom ≫ m, ?_⟩
      have h := congrArg (fun σ : Aut (Φ.obj a) ↦ σ.asIso.hom) hσ
      simp only [Functor.mapAut_apply_asIso, Functor.mapIso_hom, asIso_hom] at h
      rw [Φ.map_comp, h, Category.assoc, Groupoid.inv_comp, Category.comp_id]⟩
    have essSurj : Φ.EssSurj := ⟨fun h ↦ by
      obtain ⟨⟨a⟩, ha⟩ := h0.2 (Quotient.mk'' h)
      obtain ⟨f⟩ := (Groupoid.mk_eq_mk_iff _ _).1 ha
      exact ⟨a, ⟨asIso f⟩⟩⟩
    exact { }

end Groupoid

/-- **Layer 1.1.** For a groupoid `G`, the functor `Π₁ G ⥤ G` extending the identity is an
equivalence: `Π₁ G ≌ G`. -/
theorem isEquivalence_freeGroupoidLift_id (G : Type u) [Groupoid.{v} G] :
    (FreeGroupoid.lift (𝟭 G)).IsEquivalence :=
  (CategoryTheory.Equivalence.mk (FreeGroupoid.lift (𝟭 G)) (FreeGroupoid.of G)
    (eqToIso FreeGroupoid.lift_id_comp_of.symm) (eqToIso (FreeGroupoid.lift_spec _))
    ).isEquivalence_functor

/-- For a groupoid `G`, the localization functor `G ⥤ Π₁ G` is an equivalence. -/
theorem isEquivalence_freeGroupoidOf (G : Type u) [Groupoid.{v} G] :
    (FreeGroupoid.of G).IsEquivalence :=
  (CategoryTheory.Equivalence.mk (FreeGroupoid.lift (𝟭 G)) (FreeGroupoid.of G)
    (eqToIso FreeGroupoid.lift_id_comp_of.symm) (eqToIso (FreeGroupoid.lift_spec _))
    ).isEquivalence_inverse

/-- **Layer 1.1.** The connected components of `Π₁ A` are those of `A`. -/
theorem bijective_mapConnectedComponents_freeGroupoidOf (A : Type u) [Category.{v} A] :
    Function.Bijective (FreeGroupoid.of A).mapConnectedComponents := by
  let Φ : FreeGroupoid A ⥤ Discrete (ConnectedComponents A) :=
    FreeGroupoid.lift (ConnectedComponents.functorToDiscrete _ id)
  let r := ConnectedComponents.liftFunctor _ Φ
  have hr : Function.LeftInverse r (FreeGroupoid.of A).mapConnectedComponents := by
    rintro ⟨a⟩
    rfl
  refine ⟨hr.injective, ?_⟩
  rintro ⟨x⟩
  obtain ⟨a, rfl⟩ := FreeGroupoid.of_obj_bijective.2 x
  exact ⟨Quotient.mk'' a, rfl⟩

/-- **Layer 1.2.** `W₀`: the functors inducing a bijection on connected components. -/
def W₀ : MorphismProperty Cat.{u, u} :=
  fun _ _ F ↦ Function.Bijective F.toFunctor.mapConnectedComponents

/-- **Layer 1.2.** `W₁`: the functors inducing an equivalence of fundamental groupoids. -/
def W₁ : MorphismProperty Cat.{u, u} :=
  fun _ _ F ↦ (FreeGroupoid.map F.toFunctor).IsEquivalence

/-- The square `π₀ A → π₀ B → π₀ (Π₁ B)` and `π₀ A → π₀ (Π₁ A) → π₀ (Π₁ B)` commutes. -/
lemma mapConnectedComponents_map_comp_of {A : Type u} {B : Type u'} [Category.{v} A]
    [Category.{v'} B] (F : A ⥤ B) :
    (FreeGroupoid.map F).mapConnectedComponents ∘ (FreeGroupoid.of A).mapConnectedComponents =
      (FreeGroupoid.of B).mapConnectedComponents ∘ F.mapConnectedComponents := by
  ext ⟨a⟩
  rfl

/-- `F` is bijective on `π₀` iff `Π₁ F` is. -/
lemma bijective_mapConnectedComponents_iff {A : Type u} {B : Type u'} [Category.{v} A]
    [Category.{v'} B] (F : A ⥤ B) :
    Function.Bijective F.mapConnectedComponents ↔
      Function.Bijective (FreeGroupoid.map F).mapConnectedComponents := by
  have hA := bijective_mapConnectedComponents_freeGroupoidOf A
  have hB := bijective_mapConnectedComponents_freeGroupoidOf B
  rw [← Function.Bijective.of_comp_iff' hB, ← mapConnectedComponents_map_comp_of,
    Function.Bijective.of_comp_iff _ hA]

/-- **Layer 1.2.** `F ∈ W₁` iff `F ∈ W₀` and `F` induces bijections of the automorphism groups of
the fundamental groupoids at every object. -/
theorem W₁_iff {X Y : Cat.{u, u}} (F : X ⟶ Y) :
    W₁ F ↔ W₀ F ∧ ∀ a : X, Function.Bijective
      ((FreeGroupoid.map F.toFunctor).mapAut ((FreeGroupoid.of X).obj a)) := by
  rw [W₁, W₀, Groupoid.isEquivalence_iff_bijective,
    bijective_mapConnectedComponents_iff F.toFunctor]
  refine and_congr Iff.rfl ⟨fun h a ↦ h _, fun h x ↦ ?_⟩
  obtain ⟨a, rfl⟩ := FreeGroupoid.of_obj_bijective.2 x
  exact h a

/-- **Layer 1.2.** Between groupoids, `W₁` is the class of equivalences of categories. -/
theorem W₁_iff_isEquivalence {G H : Type u} [Groupoid.{u} G] [Groupoid.{u} H] (F : G ⥤ H) :
    W₁ F.toCatHom ↔ F.IsEquivalence := by
  have := isEquivalence_freeGroupoidOf G
  have := isEquivalence_freeGroupoidOf H
  change (FreeGroupoid.map F).IsEquivalence ↔ F.IsEquivalence
  constructor
  · intro h
    have : (F ⋙ FreeGroupoid.of H).IsEquivalence :=
      inferInstanceAs (FreeGroupoid.of G ⋙ FreeGroupoid.map F).IsEquivalence
    exact Functor.isEquivalence_of_comp_right F (FreeGroupoid.of H)
  · intro h
    have : (FreeGroupoid.of G ⋙ FreeGroupoid.map F).IsEquivalence :=
      inferInstanceAs (F ⋙ FreeGroupoid.of H).IsEquivalence
    exact Functor.isEquivalence_of_comp_left (FreeGroupoid.of G) (FreeGroupoid.map F)

/-- **Layer 1.2.** `W₁ ⊆ W₀`. -/
theorem W₁_le_W₀ : W₁.{u} ≤ W₀ := fun _ _ F h ↦ ((W₁_iff F).1 h).1

end LeanPool.HomotopyTheoryOfCategories
