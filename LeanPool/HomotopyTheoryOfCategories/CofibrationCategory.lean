/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.CategoryTheory.ConcreteCategory.Elementwise
import Mathlib.CategoryTheory.Monoidal.Mon

/-!
# Cofibration categories and Brown's factorization lemma

On a category with an initial object, cofibrations and weak equivalences (Mathlib's
`CategoryWithCofibrations` and `CategoryWithWeakEquivalences`), `IsCofibrationCategory` records
Baues' axioms C1–C3 (Baues 1989, *Algebraic homotopy*, Chapter I, (1.1)), without his axiom C4
on fibrant models. We prove Brown's factorization lemma `brown_factorization`: between cofibrant
objects, every `f : X ⟶ Y` is `i ≫ r` with `i` a cofibration and `r` a retraction of a trivial
cofibration `j`. The proof factors `(f, 𝟙) : X ⊔ Y ⟶ Y` as a cofibration followed by a weak
equivalence, the coproduct being the pushout over the initial object.

The derivator of a cofibration category and the homotopy category (roadmap Layer 11 beyond 11.2)
are not formalised.

This is Layer 11 of the roadmap *Homotopy theory of small categories*.
-/

@[expose] public section

universe v u

namespace LeanPool.HomotopyTheoryOfCategories

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

variable (C : Type u) [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C]

/-- **Layer 11.1.** Baues' axioms C1–C3 (Baues 1989, Chapter I, (1.1)). -/
class IsCofibrationCategory : Prop where
  /-- C1: isomorphisms are cofibrations. -/
  iso_cofibration : ∀ {X Y : C} (e : X ≅ Y), cofibrations C e.hom
  /-- C1: isomorphisms are weak equivalences. -/
  iso_weakEquivalence : ∀ {X Y : C} (e : X ≅ Y), weakEquivalences C e.hom
  /-- C1: weak equivalences have two-out-of-three. -/
  twoOutOfThree : (weakEquivalences C).HasTwoOutOfThreeProperty
  /-- C1: cofibrations compose. -/
  comp_cofibration : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
    cofibrations C f → cofibrations C g → cofibrations C (f ≫ g)
  /-- C2: pushouts along cofibrations exist. -/
  hasPushout : ∀ {X Y Z : C} (i : X ⟶ Y) (f : X ⟶ Z), cofibrations C i → HasPushout i f
  /-- C2: the cobase change of a cofibration is a cofibration. -/
  cofibration_cobaseChange : ∀ {X Y Z P : C} {i : X ⟶ Y} {f : X ⟶ Z} {f' : Y ⟶ P}
    {i' : Z ⟶ P}, IsPushout i f f' i' → cofibrations C i → cofibrations C i'
  /-- C2: the cobase change of a trivial cofibration is a weak equivalence. -/
  weakEquivalence_cobaseChange : ∀ {X Y Z P : C} {i : X ⟶ Y} {f : X ⟶ Z} {f' : Y ⟶ P}
    {i' : Z ⟶ P}, IsPushout i f f' i' → cofibrations C i → weakEquivalences C i →
      weakEquivalences C i'
  /-- C2: along a cofibration, the map parallel to a weak equivalence is a weak equivalence. -/
  weakEquivalence_parallel : ∀ {X Y Z P : C} {i : X ⟶ Y} {f : X ⟶ Z} {f' : Y ⟶ P}
    {i' : Z ⟶ P}, IsPushout i f f' i' → cofibrations C i → weakEquivalences C f →
      weakEquivalences C f'
  /-- C3: every map factors as a cofibration followed by a weak equivalence. -/
  factorization : ∀ {X Y : C} (f : X ⟶ Y),
    ∃ (Z : C) (i : X ⟶ Z) (p : Z ⟶ Y), cofibrations C i ∧ weakEquivalences C p ∧ i ≫ p = f

/-- **Layer 11.2.** Brown's factorization lemma between cofibrant objects: `f = i ≫ r` with `i`
a cofibration and `r` a retraction of a trivial cofibration `j`. -/
theorem brown_factorization [IsCofibrationCategory C] {X Y : C}
    (hX : cofibrations C (initial.to X)) (hY : cofibrations C (initial.to Y)) (f : X ⟶ Y) :
    ∃ (Z : C) (i : X ⟶ Z) (r : Z ⟶ Y) (j : Y ⟶ Z),
      cofibrations C i ∧ cofibrations C j ∧ weakEquivalences C j ∧ j ≫ r = 𝟙 Y ∧
        i ≫ r = f := by
  have := IsCofibrationCategory.hasPushout (initial.to X) (initial.to Y) hX
  have hpo : IsPushout (initial.to X) (initial.to Y) (pushout.inl _ _) (pushout.inr _ _) :=
    IsPushout.of_hasPushout _ _
  have hinr : cofibrations C (pushout.inr (initial.to X) (initial.to Y)) :=
    IsCofibrationCategory.cofibration_cobaseChange hpo hX
  have hinl : cofibrations C (pushout.inl (initial.to X) (initial.to Y)) :=
    IsCofibrationCategory.cofibration_cobaseChange hpo.flip hY
  obtain ⟨Z, k, r, hk, hr, hkr⟩ := IsCofibrationCategory.factorization
    (pushout.desc f (𝟙 Y) (initial.hom_ext _ _) : pushout (initial.to X) (initial.to Y) ⟶ Y)
  have hjr : (pushout.inr _ _ ≫ k) ≫ r = 𝟙 Y := by simp [hkr]
  have := IsCofibrationCategory.twoOutOfThree (C := C)
  refine ⟨Z, pushout.inl _ _ ≫ k, r, pushout.inr _ _ ≫ k,
    IsCofibrationCategory.comp_cofibration _ _ hinl hk,
    IsCofibrationCategory.comp_cofibration _ _ hinr hk, ?_, hjr, by simp [hkr]⟩
  refine (weakEquivalences C).of_postcomp _ r hr ?_
  rw [hjr]
  exact IsCofibrationCategory.iso_weakEquivalence (Iso.refl Y)

end LeanPool.HomotopyTheoryOfCategories
