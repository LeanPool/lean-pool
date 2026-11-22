/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Direct sums of distinguished triangles

The direct sum `T₁ ⊞ T₂` of two triangles is their binary product in the category of triangles,
so it is distinguished when `T₁` and `T₂` are (`productTriangle_distinguished`).
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Pretriangulated

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [HasBinaryBiproducts C]
  (T₁ T₂ : Triangle C)

/-- The direct sum of two triangles. -/
noncomputable def triangleBiprod : Triangle C :=
  Triangle.mk (biprod.map T₁.mor₁ T₂.mor₁) (biprod.map T₁.mor₂ T₂.mor₂)
    (biprod.desc (T₁.mor₃ ≫ (biprod.inl : T₁.obj₁ ⟶ T₁.obj₁ ⊞ T₂.obj₁)⟦(1 : ℤ)⟧')
      (T₂.mor₃ ≫ (biprod.inr : T₂.obj₁ ⟶ T₁.obj₁ ⊞ T₂.obj₁)⟦(1 : ℤ)⟧'))

/-- The first projection `T₁ ⊞ T₂ ⟶ T₁`. -/
@[simps]
noncomputable def triangleBiprodFst : triangleBiprod T₁ T₂ ⟶ T₁ where
  hom₁ := biprod.fst
  hom₂ := biprod.fst
  hom₃ := biprod.fst
  comm₁ := by
    dsimp [triangleBiprod]
    rw [biprod.map_fst]
  comm₂ := by
    dsimp [triangleBiprod]
    rw [biprod.map_fst]
  comm₃ := by
    dsimp [triangleBiprod]
    apply biprod.hom_ext'
    · simp [← Functor.map_comp]
    · simp [← Functor.map_comp]

/-- The second projection `T₁ ⊞ T₂ ⟶ T₂`. -/
@[simps]
noncomputable def triangleBiprodSnd : triangleBiprod T₁ T₂ ⟶ T₂ where
  hom₁ := biprod.snd
  hom₂ := biprod.snd
  hom₃ := biprod.snd
  comm₁ := by
    dsimp [triangleBiprod]
    rw [biprod.map_snd]
  comm₂ := by
    dsimp [triangleBiprod]
    rw [biprod.map_snd]
  comm₃ := by
    dsimp [triangleBiprod]
    apply biprod.hom_ext'
    · simp [← Functor.map_comp]
    · simp [← Functor.map_comp]

/-- The lift of two morphisms of triangles into `T₁ ⊞ T₂`. -/
@[simps]
noncomputable def triangleBiprodLift {T : Triangle C} (f : T ⟶ T₁) (g : T ⟶ T₂) :
    T ⟶ triangleBiprod T₁ T₂ where
  hom₁ := biprod.lift f.hom₁ g.hom₁
  hom₂ := biprod.lift f.hom₂ g.hom₂
  hom₃ := biprod.lift f.hom₃ g.hom₃
  comm₁ := by
    dsimp [triangleBiprod]
    apply biprod.hom_ext <;> simp [f.comm₁, g.comm₁]
  comm₂ := by
    dsimp [triangleBiprod]
    apply biprod.hom_ext <;> simp [f.comm₂, g.comm₂]
  comm₃ := by
    dsimp [triangleBiprod]
    rw [biprod.lift_desc, biprod.lift_eq, Functor.map_add, Functor.map_comp, Functor.map_comp,
      Preadditive.comp_add, ← Category.assoc, ← Category.assoc, f.comm₃, g.comm₃,
      Category.assoc, Category.assoc]

/-- `T₁ ⊞ T₂` is a binary product in the category of triangles. -/
noncomputable def isLimitTriangleBiprod :
    IsLimit (BinaryFan.mk (triangleBiprodFst T₁ T₂) (triangleBiprodSnd T₁ T₂)) :=
  BinaryFan.IsLimit.mk _ (fun f g => triangleBiprodLift T₁ T₂ f g)
    (fun f g => by ext <;> exact biprod.lift_fst _ _)
    (fun f g => by ext <;> exact biprod.lift_snd _ _)
    (fun f g m h₁ h₂ => by
      ext
      · apply biprod.hom_ext
        · exact (congrArg TriangleMorphism.hom₁ h₁).trans (biprod.lift_fst _ _).symm
        · exact (congrArg TriangleMorphism.hom₁ h₂).trans (biprod.lift_snd _ _).symm
      · apply biprod.hom_ext
        · exact (congrArg TriangleMorphism.hom₂ h₁).trans (biprod.lift_fst _ _).symm
        · exact (congrArg TriangleMorphism.hom₂ h₂).trans (biprod.lift_snd _ _).symm
      · apply biprod.hom_ext
        · exact (congrArg TriangleMorphism.hom₃ h₁).trans (biprod.lift_fst _ _).symm
        · exact (congrArg TriangleMorphism.hom₃ h₂).trans (biprod.lift_snd _ _).symm)

omit [HasZeroObject C] [Pretriangulated C] in
lemma comp_shift_biprod_lift {X Y Z₁ Z₂ : C} (φ : X ⟶ Y⟦(1 : ℤ)⟧) (a : Y ⟶ Z₁) (b : Y ⟶ Z₂) :
    φ ≫ (biprod.lift a b)⟦(1 : ℤ)⟧' =
      (φ ≫ a⟦(1 : ℤ)⟧') ≫ (biprod.inl : Z₁ ⟶ Z₁ ⊞ Z₂)⟦(1 : ℤ)⟧' +
        (φ ≫ b⟦(1 : ℤ)⟧') ≫ (biprod.inr : Z₂ ⟶ Z₁ ⊞ Z₂)⟦(1 : ℤ)⟧' := by
  rw [biprod.lift_eq, Functor.map_add, Functor.map_comp, Functor.map_comp, Preadditive.comp_add,
    Category.assoc, Category.assoc]

/-- The direct sum of two distinguished triangles is distinguished. -/
lemma triangleBiprod_distinguished (h₁ : T₁ ∈ distTriang C) (h₂ : T₂ ∈ distTriang C) :
    triangleBiprod T₁ T₂ ∈ distTriang C :=
  isomorphic_distinguished _
    (productTriangle_distinguished (pairFunction T₁ T₂) (by rintro (_ | _) <;> assumption)) _
    (IsLimit.conePointUniqueUpToIso (isLimitTriangleBiprod T₁ T₂)
      (productTriangle.isLimitFan (pairFunction T₁ T₂)))

end ExtriangulatedRealization
