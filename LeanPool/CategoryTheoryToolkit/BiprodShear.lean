/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Preadditive.OfBiproducts

/-!
# The shear map of `X ⊞ X` and a criterion for additivity

In a category with zero morphisms and binary biproducts, whose hom-sets are then commutative
monoids (`SemiadditiveOfBinaryBiproducts.addCommMonoidHomOfHasBinaryBiproducts`), the shear map
`(x, y) ↦ (x, x + y)` of `X ⊞ X` has zero kernel and zero cokernel; if it is invertible, `𝟙 X`
has an additive inverse. Hence, if every morphism with zero kernel and zero cokernel is
invertible, the category is preadditive, with the addition given by the biproducts.

## Main statements

* `SemiadditiveOfBinaryBiproducts.shear` and its action on lifts and descents;
* `eq_zero_of_comp_shear_eq_zero`, `eq_zero_of_shear_comp_eq_zero`: zero kernel and cokernel;
* `exists_add_id_eq_zero_of_isIso`: if the shear map is invertible, `𝟙 X` has an additive
  inverse;
* `SemiadditiveOfBinaryBiproducts.WeakMonoEpiInvertible`, `preadditiveOfWeakMonoEpiInvertible`,
  `preadditiveOfWeakMonoEpiInvertible_add`: the criterion for additivity.
-/

@[expose] public section

namespace CategoryTheory.SemiadditiveOfBinaryBiproducts

open Limits

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasBinaryBiproducts C]

attribute [local instance] addCommMonoidHomOfHasBinaryBiproducts

/-- The shear map `(x, y) ↦ (x, x + y)` of `X ⊞ X`, the matrix `(1 0; 1 1)`. -/
noncomputable def shear (X : C) : X ⊞ X ⟶ X ⊞ X :=
  biprod.lift biprod.fst (biprod.desc (𝟙 X) (𝟙 X))

theorem lift_comp_shear {Z X : C} (g₁ g₂ : Z ⟶ X) :
    biprod.lift g₁ g₂ ≫ shear X = biprod.lift g₁ (g₁ + g₂) := by
  ext
  · simp [shear]
  · simp [shear, add_eq_left_addition]

theorem inl_comp_shear (X : C) : biprod.inl ≫ shear X = biprod.lift (𝟙 X) (𝟙 X) := by
  ext <;> simp [shear]

theorem inr_comp_shear (X : C) : biprod.inr ≫ shear X = biprod.inr := by
  ext <;> simp [shear]

theorem shear_comp_desc {X Z : C} (h₁ h₂ : X ⟶ Z) :
    shear X ≫ biprod.desc h₁ h₂ = biprod.desc (h₁ + h₂) h₂ := by
  ext
  · rw [← Category.assoc, inl_comp_shear, biprod.inl_desc, add_eq_right_addition]
  · rw [← Category.assoc, inr_comp_shear, biprod.inr_desc, biprod.inr_desc]

theorem eq_zero_of_comp_shear_eq_zero (X : C) ⦃Z : C⦄ (g : Z ⟶ X ⊞ X) (hg : g ≫ shear X = 0) :
    g = 0 := by
  have e : g = biprod.lift (g ≫ biprod.fst) (g ≫ biprod.snd) := by ext <;> simp
  rw [e] at hg ⊢
  rw [lift_comp_shear] at hg
  have h₁ := congrArg (· ≫ biprod.fst) hg
  have h₂ := congrArg (· ≫ biprod.snd) hg
  simp only [biprod.lift_fst, biprod.lift_snd, zero_comp] at h₁ h₂
  rw [h₁, zero_add] at h₂
  ext <;> simp [h₁, h₂]

theorem eq_zero_of_shear_comp_eq_zero (X : C) ⦃Z : C⦄ (h : X ⊞ X ⟶ Z) (hh : shear X ≫ h = 0) :
    h = 0 := by
  have e : h = biprod.desc (biprod.inl ≫ h) (biprod.inr ≫ h) := by ext <;> simp
  rw [e] at hh ⊢
  rw [shear_comp_desc] at hh
  have h₁ := congrArg (biprod.inl ≫ ·) hh
  have h₂ := congrArg (biprod.inr ≫ ·) hh
  simp only [biprod.inl_desc, biprod.inr_desc, comp_zero] at h₁ h₂
  rw [h₂, add_zero] at h₁
  ext <;> simp [h₁, h₂]

theorem exists_add_id_eq_zero_of_isIso (X : C) [IsIso (shear X)] : ∃ g : X ⟶ X, 𝟙 X + g = 0 := by
  refine ⟨biprod.inl ≫ inv (shear X) ≫ biprod.snd, ?_⟩
  have e : biprod.inl ≫ inv (shear X) = biprod.lift (biprod.inl ≫ inv (shear X) ≫ biprod.fst)
      (biprod.inl ≫ inv (shear X) ≫ biprod.snd) := by ext <;> simp
  have h := congrArg (· ≫ shear X) e
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, lift_comp_shear] at h
  have h₁ := congrArg (· ≫ biprod.fst) h
  have h₂ := congrArg (· ≫ biprod.snd) h
  simp only [biprod.inl_fst, biprod.inl_snd, biprod.lift_fst, biprod.lift_snd] at h₁ h₂
  rw [← h₁] at h₂
  exact h₂.symm

/-- Every morphism with zero kernel and zero cokernel (in the weak sense `g ≫ f = 0 → g = 0`,
`f ≫ g = 0 → g = 0`) is invertible. -/
def WeakMonoEpiInvertible (C : Type*) [Category C] [HasZeroMorphisms C] : Prop :=
  ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ ⦃Z : C⦄ (g : Z ⟶ X), g ≫ f = 0 → g = 0) →
    (∀ ⦃Z : C⦄ (g : Y ⟶ Z), f ≫ g = 0 → g = 0) → IsIso f

theorem exists_add_eq_zero_of_weakMonoEpiInvertible (H : WeakMonoEpiInvertible C) {X Y : C}
    (f : X ⟶ Y) : ∃ g : X ⟶ Y, f + g = 0 := by
  have := H (shear X) (eq_zero_of_comp_shear_eq_zero X) (eq_zero_of_shear_comp_eq_zero X)
  obtain ⟨g, hg⟩ := exists_add_id_eq_zero_of_isIso X
  refine ⟨g ≫ f, ?_⟩
  have := congrArg (· ≫ f) hg
  simpa [add_comp] using this

/-- Under the hypothesis `WeakMonoEpiInvertible C`, the commutative monoid structure on the
hom-sets given by the biproducts is that of a preadditive category. -/
@[instance_reducible]
noncomputable def preadditiveOfWeakMonoEpiInvertible (H : WeakMonoEpiInvertible C) :
    Preadditive C where
  homGroup X Y :=
    letI : Neg (X ⟶ Y) := ⟨fun f ↦ (exists_add_eq_zero_of_weakMonoEpiInvertible H f).choose⟩
    { AddGroup.ofLeftAxioms add_assoc zero_add fun f ↦ by
        rw [add_comm]
        exact (exists_add_eq_zero_of_weakMonoEpiInvertible H f).choose_spec with
      add_comm := add_comm }
  add_comp _ _ _ _ _ _ := add_comp _ _ _
  comp_add _ _ _ _ _ _ := comp_add _ _ _

/-- The addition of `preadditiveOfWeakMonoEpiInvertible H` is the one given by the biproducts. -/
theorem preadditiveOfWeakMonoEpiInvertible_add (H : WeakMonoEpiInvertible C) {X Y : C}
    (f g : X ⟶ Y) :
    @HAdd.hAdd (X ⟶ Y) (X ⟶ Y) (X ⟶ Y)
      (@instHAdd _ (@Preadditive.homGroup C _ (preadditiveOfWeakMonoEpiInvertible H) X Y).toAdd)
        f g = f + g :=
  rfl

end CategoryTheory.SemiadditiveOfBinaryBiproducts
